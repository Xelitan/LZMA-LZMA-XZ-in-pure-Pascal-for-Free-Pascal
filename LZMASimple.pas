unit LZMASimple;

{$IFDEF FPC}{$mode delphi}{$ENDIF}
{$Q-}{$R-}

interface

//LZMA + LZMA2
//Author: www.xelitan.com
//License: MIT

uses Classes, SysUtils;

type
  ELZMAError = class(Exception);
  TXZCheckType = (xzNone = 0, xzCRC32 = 1, xzCRC64 = 4, xzSHA256 = 10);
  TBCJFilter   = (bcjNone, bcjX86, bcjPowerPC, bcjIA64, bcjARM,
                  bcjARMThumb, bcjSPARC, bcjARM64);

procedure LZMACompress(const InStr, OutStr: TStream);
procedure LZMADeCompress(const InStr, OutStr: TStream);

procedure LZMACompressFile(const InFile, OutFile: String);
procedure LZMADeCompressFile(const InFile, OutFile: String); //unpacks .lzma

procedure LZMA2CompressFile(const InFile, OutFile: String);
procedure LZMA2DeCompressFile(const InFile, OutFile: String); //unpacks .xz

procedure LZMA2Compress(const InStr, OutStr: TStream);
procedure LZMA2DeCompress(const InStr, OutStr: TStream);
procedure LZMA2CompressEx(const InStr, OutStr: TStream; Level: Integer = 6;
                           Check: TXZCheckType = xzCRC32;
                           BCJ: TBCJFilter = bcjNone;
                           DeltaDist: Integer = 0);

function LZMA(const Uncompressed: AnsiString): AnsiString;
function UnLZMA(const Compressed: AnsiString): AnsiString;

function XZ(const Uncompressed: AnsiString): AnsiString;
function UnXZ(const Compressed: AnsiString): AnsiString;

implementation

uses SHA256;

{$IFNDEF FPC}
{$POINTERMATH ON}
type
  TStreamHelper = class helper for TStream
    procedure WriteByte(b: Byte);
    function ReadByte: Byte;
  end;
procedure TStreamHelper.WriteByte(b: Byte); begin WriteBuffer(b, 1); end;
function TStreamHelper.ReadByte: Byte; begin ReadBuffer(Result, 1); end;
{$ENDIF}

// ===========================================================================
// Endian helpers
// ===========================================================================

function Read32LE(p: PByte): LongWord; inline;
begin
  Result := LongWord(p[0]) or (LongWord(p[1]) shl 8) or
            (LongWord(p[2]) shl 16) or (LongWord(p[3]) shl 24);
end;

procedure Write32LE(p: PByte; v: LongWord); inline;
begin
  p[0]:=v; 
  p[1]:=v shr 8; 
  p[2]:=v shr 16; 
  p[3]:=v shr 24; 
end;

function Read32BE(p: PByte): LongWord; inline;
begin
  Result := (LongWord(p[0]) shl 24) or (LongWord(p[1]) shl 16) or
            (LongWord(p[2]) shl 8) or LongWord(p[3]);
end;

procedure Write32BE(p: PByte; v: LongWord); inline;
begin 
  p[0]:=v shr 24; 
  p[1]:=v shr 16; 
  p[2]:=v shr 8; 
  p[3]:=v; 
end;

// ===========================================================================
// CRC32
// ===========================================================================

var CRCTable: array[0..255] of LongWord;

procedure BuildCRCTable;
var i,j: Integer; c: LongWord;
begin
  for i:=0 to 255 do begin
    c:=LongWord(i);
    for j:=0 to 7 do
      if (c and 1)<>0 then c:=$EDB88320 xor (c shr 1) else c:=c shr 1;
    CRCTable[i]:=c;
  end;
end;

function CRC32Update(crc: LongWord; buf: PByte; len: LongWord): LongWord;
begin
  crc := crc xor $FFFFFFFF;
  while len > 0 do begin
    crc := CRCTable[Byte(crc) xor buf^] xor (crc shr 8);
    Inc(buf); Dec(len);
  end;
  Result := crc xor $FFFFFFFF;
end;

// ===========================================================================
// CRC64 — XZ variant (poly=0xC96C5795D7870F42, init=all-1s, finalXOR=all-1s)
// ===========================================================================

const CRC64Table: array[0..255] of UInt64 = (
  UInt64($0000000000000000),UInt64($B32E4CBE03A75F6F),UInt64($F4843657A840A05B),UInt64($47AA7AE9ABE7FF34),
  UInt64($7BD0C384FF8F5E33),UInt64($C8FE8F3AFC28015C),UInt64($8F54F5D357CFFE68),UInt64($3C7AB96D5468A107),
  UInt64($F7A18709FF1EBC66),UInt64($448FCBB7FCB9E309),UInt64($0325B15E575E1C3D),UInt64($B00BFDE054F94352),
  UInt64($8C71448D0091E255),UInt64($3F5F08330336BD3A),UInt64($78F572DAA8D1420E),UInt64($CBDB3E64AB761D61),
  UInt64($7D9BA13851336649),UInt64($CEB5ED8652943926),UInt64($891F976FF973C612),UInt64($3A31DBD1FAD4997D),
  UInt64($064B62BCAEBC387A),UInt64($B5652E02AD1B6715),UInt64($F2CF54EB06FC9821),UInt64($41E11855055BC74E),
  UInt64($8A3A2631AE2DDA2F),UInt64($39146A8FAD8A8540),UInt64($7EBE1066066D7A74),UInt64($CD905CD805CA251B),
  UInt64($F1EAE5B551A2841C),UInt64($42C4A90B5205DB73),UInt64($056ED3E2F9E22447),UInt64($B6409F5CFA457B28),
  UInt64($FB374270A266CC92),UInt64($48190ECEA1C193FD),UInt64($0FB374270A266CC9),UInt64($BC9D3899098133A6),
  UInt64($80E781F45DE992A1),UInt64($33C9CD4A5E4ECDCE),UInt64($7463B7A3F5A932FA),UInt64($C74DFB1DF60E6D95),
  UInt64($0C96C5795D7870F4),UInt64($BFB889C75EDF2F9B),UInt64($F812F32EF538D0AF),UInt64($4B3CBF90F69F8FC0),
  UInt64($774606FDA2F72EC7),UInt64($C4684A43A15071A8),UInt64($83C230AA0AB78E9C),UInt64($30EC7C140910D1F3),
  UInt64($86ACE348F355AADB),UInt64($3582AFF6F0F2F5B4),UInt64($7228D51F5B150A80),UInt64($C10699A158B255EF),
  UInt64($FD7C20CC0CDAF4E8),UInt64($4E526C720F7DAB87),UInt64($09F8169BA49A54B3),UInt64($BAD65A25A73D0BDC),
  UInt64($710D64410C4B16BD),UInt64($C22328FF0FEC49D2),UInt64($85895216A40BB6E6),UInt64($36A71EA8A7ACE989),
  UInt64($0ADDA7C5F3C4488E),UInt64($B9F3EB7BF06317E1),UInt64($FE5991925B84E8D5),UInt64($4D77DD2C5823B7BA),
  UInt64($64B62BCAEBC387A1),UInt64($D7986774E864D8CE),UInt64($90321D9D438327FA),UInt64($231C512340247895),
  UInt64($1F66E84E144CD992),UInt64($AC48A4F017EB86FD),UInt64($EBE2DE19BC0C79C9),UInt64($58CC92A7BFAB26A6),
  UInt64($9317ACC314DD3BC7),UInt64($2039E07D177A64A8),UInt64($67939A94BC9D9B9C),UInt64($D4BDD62ABF3AC4F3),
  UInt64($E8C76F47EB5265F4),UInt64($5BE923F9E8F53A9B),UInt64($1C4359104312C5AF),UInt64($AF6D15AE40B59AC0),
  UInt64($192D8AF2BAF0E1E8),UInt64($AA03C64CB957BE87),UInt64($EDA9BCA512B041B3),UInt64($5E87F01B11171EDC),
  UInt64($62FD4976457FBFDB),UInt64($D1D305C846D8E0B4),UInt64($96797F21ED3F1F80),UInt64($2557339FEE9840EF),
  UInt64($EE8C0DFB45EE5D8E),UInt64($5DA24145464902E1),UInt64($1A083BACEDAEFDD5),UInt64($A9267712EE09A2BA),
  UInt64($955CCE7FBA6103BD),UInt64($267282C1B9C65CD2),UInt64($61D8F8281221A3E6),UInt64($D2F6B4961186FC89),
  UInt64($9F8169BA49A54B33),UInt64($2CAF25044A02145C),UInt64($6B055FEDE1E5EB68),UInt64($D82B1353E242B407),
  UInt64($E451AA3EB62A1500),UInt64($577FE680B58D4A6F),UInt64($10D59C691E6AB55B),UInt64($A3FBD0D71DCDEA34),
  UInt64($6820EEB3B6BBF755),UInt64($DB0EA20DB51CA83A),UInt64($9CA4D8E41EFB570E),UInt64($2F8A945A1D5C0861),
  UInt64($13F02D374934A966),UInt64($A0DE61894A93F609),UInt64($E7741B60E174093D),UInt64($545A57DEE2D35652),
  UInt64($E21AC88218962D7A),UInt64($5134843C1B317215),UInt64($169EFED5B0D68D21),UInt64($A5B0B26BB371D24E),
  UInt64($99CA0B06E7197349),UInt64($2AE447B8E4BE2C26),UInt64($6D4E3D514F59D312),UInt64($DE6071EF4CFE8C7D),
  UInt64($15BB4F8BE788911C),UInt64($A6950335E42FCE73),UInt64($E13F79DC4FC83147),UInt64($521135624C6F6E28),
  UInt64($6E6B8C0F1807CF2F),UInt64($DD45C0B11BA09040),UInt64($9AEFBA58B0476F74),UInt64($29C1F6E6B3E0301B),
  UInt64($C96C5795D7870F42),UInt64($7A421B2BD420502D),UInt64($3DE861C27FC7AF19),UInt64($8EC62D7C7C60F076),
  UInt64($B2BC941128085171),UInt64($0192D8AF2BAF0E1E),UInt64($4638A2468048F12A),UInt64($F516EEF883EFAE45),
  UInt64($3ECDD09C2899B324),UInt64($8DE39C222B3EEC4B),UInt64($CA49E6CB80D9137F),UInt64($7967AA75837E4C10),
  UInt64($451D1318D716ED17),UInt64($F6335FA6D4B1B278),UInt64($B199254F7F564D4C),UInt64($02B769F17CF11223),
  UInt64($B4F7F6AD86B4690B),UInt64($07D9BA1385133664),UInt64($4073C0FA2EF4C950),UInt64($F35D8C442D53963F),
  UInt64($CF273529793B3738),UInt64($7C0979977A9C6857),UInt64($3BA3037ED17B9763),UInt64($888D4FC0D2DCC80C),
  UInt64($435671A479AAD56D),UInt64($F0783D1A7A0D8A02),UInt64($B7D247F3D1EA7536),UInt64($04FC0B4DD24D2A59),
  UInt64($3886B22086258B5E),UInt64($8BA8FE9E8582D431),UInt64($CC0284772E652B05),UInt64($7F2CC8C92DC2746A),
  UInt64($325B15E575E1C3D0),UInt64($8175595B76469CBF),UInt64($C6DF23B2DDA1638B),UInt64($75F16F0CDE063CE4),
  UInt64($498BD6618A6E9DE3),UInt64($FAA59ADF89C9C28C),UInt64($BD0FE036222E3DB8),UInt64($0E21AC88218962D7),
  UInt64($C5FA92EC8AFF7FB6),UInt64($76D4DE52895820D9),UInt64($317EA4BB22BFDFED),UInt64($8250E80521188082),
  UInt64($BE2A516875702185),UInt64($0D041DD676D77EEA),UInt64($4AAE673FDD3081DE),UInt64($F9802B81DE97DEB1),
  UInt64($4FC0B4DD24D2A599),UInt64($FCEEF8632775FAF6),UInt64($BB44828A8C9205C2),UInt64($086ACE348F355AAD),
  UInt64($34107759DB5DFBAA),UInt64($873E3BE7D8FAA4C5),UInt64($C094410E731D5BF1),UInt64($73BA0DB070BA049E),
  UInt64($B86133D4DBCC19FF),UInt64($0B4F7F6AD86B4690),UInt64($4CE50583738CB9A4),UInt64($FFCB493D702BE6CB),
  UInt64($C3B1F050244347CC),UInt64($709FBCEE27E418A3),UInt64($3735C6078C03E797),UInt64($841B8AB98FA4B8F8),
  UInt64($ADDA7C5F3C4488E3),UInt64($1EF430E13FE3D78C),UInt64($595E4A08940428B8),UInt64($EA7006B697A377D7),
  UInt64($D60ABFDBC3CBD6D0),UInt64($6524F365C06C89BF),UInt64($228E898C6B8B768B),UInt64($91A0C532682C29E4),
  UInt64($5A7BFB56C35A3485),UInt64($E955B7E8C0FD6BEA),UInt64($AEFFCD016B1A94DE),UInt64($1DD181BF68BDCBB1),
  UInt64($21AB38D23CD56AB6),UInt64($9285746C3F7235D9),UInt64($D52F0E859495CAED),UInt64($6601423B97329582),
  UInt64($D041DD676D77EEAA),UInt64($636F91D96ED0B1C5),UInt64($24C5EB30C5374EF1),UInt64($97EBA78EC690119E),
  UInt64($AB911EE392F8B099),UInt64($18BF525D915FEFF6),UInt64($5F1528B43AB810C2),UInt64($EC3B640A391F4FAD),
  UInt64($27E05A6E926952CC),UInt64($94CE16D091CE0DA3),UInt64($D3646C393A29F297),UInt64($604A2087398EADF8),
  UInt64($5C3099EA6DE60CFF),UInt64($EF1ED5546E415390),UInt64($A8B4AFBDC5A6ACA4),UInt64($1B9AE303C601F3CB),
  UInt64($56ED3E2F9E224471),UInt64($E5C372919D851B1E),UInt64($A26908783662E42A),UInt64($114744C635C5BB45),
  UInt64($2D3DFDAB61AD1A42),UInt64($9E13B115620A452D),UInt64($D9B9CBFCC9EDBA19),UInt64($6A978742CA4AE576),
  UInt64($A14CB926613CF817),UInt64($1262F598629BA778),UInt64($55C88F71C97C584C),UInt64($E6E6C3CFCADB0723),
  UInt64($DA9C7AA29EB3A624),UInt64($69B2361C9D14F94B),UInt64($2E184CF536F3067F),UInt64($9D36004B35545910),
  UInt64($2B769F17CF112238),UInt64($9858D3A9CCB67D57),UInt64($DFF2A94067518263),UInt64($6CDCE5FE64F6DD0C),
  UInt64($50A65C93309E7C0B),UInt64($E388102D33392364),UInt64($A4226AC498DEDC50),UInt64($170C267A9B79833F),
  UInt64($DCD7181E300F9E5E),UInt64($6FF954A033A8C131),UInt64($28532E49984F3E05),UInt64($9B7D62F79BE8616A),
  UInt64($A707DB9ACF80C06D),UInt64($14299724CC279F02),UInt64($5383EDCD67C06036),UInt64($E0ADA17364673F59)
);

function CRC64Update(crc: UInt64; buf: PByte; len: LongWord): UInt64;
begin
  crc := crc xor UInt64($FFFFFFFFFFFFFFFF);
  while len > 0 do begin
    crc := CRC64Table[Byte(crc) xor buf^] xor (crc shr 8);
    Inc(buf); Dec(len);
  end;
  Result := crc xor UInt64($FFFFFFFFFFFFFFFF);
end;

// ===========================================================================
// Range coder constants
// ===========================================================================

const
  RC_BIT_MODEL_TOTAL_BITS = 11;
  RC_BIT_MODEL_TOTAL      = 1 shl RC_BIT_MODEL_TOTAL_BITS;
  RC_MOVE_BITS            = 5;
  RC_TOP_VALUE            = $01000000;
  PROB_INIT_VAL           = RC_BIT_MODEL_TOTAL div 2;

type TProb = Word;

// ===========================================================================
// LZMA constants
// ===========================================================================

const
  LZMA_NUM_STATES    = 12;
  LITERAL_CODER_SIZE = $300;
  DIST_STATES        = 4;
  DIST_SLOT_BITS     = 6;
  DIST_SLOTS         = 1 shl DIST_SLOT_BITS;
  DIST_MODEL_START   = 4;
  DIST_MODEL_END     = 14;
  FULL_DISTANCES     = 1 shl (DIST_MODEL_END div 2);
  ALIGN_BITS         = 4;
  ALIGN_SIZE         = 1 shl ALIGN_BITS;
  ALIGN_MASK         = ALIGN_SIZE - 1;
  MATCH_LEN_MIN      = 2;
  MATCH_LEN_MAX      = 273;
  LEN_LOW_BITS       = 3;
  LEN_LOW_SYMS       = 1 shl LEN_LOW_BITS;
  LEN_MID_BITS       = 3;
  LEN_MID_SYMS       = 1 shl LEN_MID_BITS;
  LEN_HIGH_BITS      = 8;
  LEN_HIGH_SYMS      = 1 shl LEN_HIGH_BITS;
  LZMA2_UNCOMPRESSED_MAX = (1 shl 21) - 1;
  LZ_DICT_REPEAT_MAX = 288;
  LZ_DICT_INIT_POS   = 2 * LZ_DICT_REPEAT_MAX;

// ===========================================================================
// Preset levels 0-9
// ===========================================================================

type
  TMatchFinderKind = (mfkHC3, mfkHC4, mfkBT2, mfkBT3, mfkBT4);

  TLZMAPreset = record
    DictSizeProp: Byte;   // xz dict prop byte
    DictSize: LongWord;   // actual dict size
    MFKind: TMatchFinderKind;
    NiceLen: Integer;
    MaxDepth: Integer;
  end;

const
  LZMA_PRESETS: array[0..9] of TLZMAPreset = (
    (DictSizeProp:12; DictSize:  262144; MFKind:mfkHC3; NiceLen:32; MaxDepth:4),   // 0 256KB
    (DictSizeProp:16; DictSize: 1048576; MFKind:mfkHC4; NiceLen:32; MaxDepth:4),   // 1 1MB
    (DictSizeProp:18; DictSize: 2097152; MFKind:mfkHC4; NiceLen:32; MaxDepth:4),   // 2 2MB
    (DictSizeProp:20; DictSize: 4194304; MFKind:mfkHC4; NiceLen:32; MaxDepth:4),   // 3 4MB
    (DictSizeProp:20; DictSize: 4194304; MFKind:mfkHC4; NiceLen:32; MaxDepth:8),   // 4 4MB
    (DictSizeProp:22; DictSize: 8388608; MFKind:mfkBT4; NiceLen:32; MaxDepth:32),  // 5 8MB
    (DictSizeProp:22; DictSize: 8388608; MFKind:mfkBT4; NiceLen:64; MaxDepth:32),  // 6 8MB default
    (DictSizeProp:24; DictSize:16777216; MFKind:mfkBT4; NiceLen:64; MaxDepth:64),  // 7 16MB
    (DictSizeProp:26; DictSize:33554432; MFKind:mfkBT4; NiceLen:64; MaxDepth:64),  // 8 32MB
    (DictSizeProp:28; DictSize:67108864; MFKind:mfkBT4; NiceLen:64; MaxDepth:64)   // 9 64MB
  );

// ===========================================================================
// Distance slot
// ===========================================================================

function DistSlot(dist: LongWord): LongWord;
var msb, v: LongWord;
begin
  if dist <= 3 then begin Result:=dist; Exit; end;
  msb:=0; v:=dist;
  while v > 1 do begin v:=v shr 1; Inc(msb); end;
  Result:=2*msb+((dist shr (msb-1)) and 1);
end;

// ===========================================================================
// Range Encoder
// ===========================================================================

type
  TRangeEnc = record
    Low: Int64; 
    Range: LongWord; 
    Cache: Byte; 
    CacheSize: Int64;
    OutStream: TStream;
  end;

procedure RCEncInit(var rc: TRangeEnc; OutStr: TStream);
begin 
  rc.Low:=0; 
  rc.Range:=$FFFFFFFF; 
  rc.Cache:=0; 
  rc.CacheSize:=1; 
  rc.OutStream:=OutStr; 
end;

procedure RCShiftLow(var rc: TRangeEnc);
var b: Byte;
begin
  if (LongWord(rc.Low)<$FF000000) or (rc.Low shr 32<>0) then 
  begin
    b:=rc.Cache+Byte(rc.Low shr 32);
    rc.Cache:=Byte(rc.Low shr 24);
    rc.OutStream.WriteByte(b);
    b:=Byte($FF+(rc.Low shr 32));
    while rc.CacheSize>1 do 
    begin 
      rc.OutStream.WriteByte(b); 
      Dec(rc.CacheSize); 
    end;
  end else Inc(rc.CacheSize);
  rc.Low:=LongWord(rc.Low) shl 8;
end;

procedure RCEncBit(var rc: TRangeEnc; var prob: TProb; bit: Integer);
var bound: LongWord;
begin
  bound:=(rc.Range shr RC_BIT_MODEL_TOTAL_BITS)*prob;
  if bit=0 then begin rc.Range:=bound; prob:=prob+((RC_BIT_MODEL_TOTAL-prob) shr RC_MOVE_BITS);
  end else begin rc.Low:=rc.Low+bound; rc.Range:=rc.Range-bound; prob:=prob-(prob shr RC_MOVE_BITS); end;
  if rc.Range<RC_TOP_VALUE then begin rc.Range:=rc.Range shl 8; RCShiftLow(rc); end;
end;

procedure RCEncBitTree(var rc: TRangeEnc; probs: PWord; numBits: Integer; symbol: LongWord);
var i: Integer; m: LongWord; bit: Integer;
begin
  m:=1;
  for i:=numBits-1 downto 0 do begin
    bit:=(symbol shr i) and 1; RCEncBit(rc, probs[m], bit); m:=(m shl 1) or LongWord(bit);
  end;
end;

procedure RCEncBitTreeRev(var rc: TRangeEnc; probs: PWord; numBits: Integer; symbol: LongWord);
var i: Integer; m: LongWord; bit: Integer;
begin
  m:=1;
  for i:=0 to numBits-1 do begin
    bit:=(symbol shr i) and 1; RCEncBit(rc, probs[m], bit); m:=(m shl 1) or LongWord(bit);
  end;
end;

procedure RCEncDirect(var rc: TRangeEnc; value: LongWord; numBits: Integer);
var i: Integer;
begin
  for i:=numBits-1 downto 0 do begin
    rc.Range:=rc.Range shr 1;
    if ((value shr i) and 1)<>0 then rc.Low:=rc.Low+rc.Range;
    if rc.Range<RC_TOP_VALUE then begin rc.Range:=rc.Range shl 8; RCShiftLow(rc); end;
  end;
end;

procedure RCEncFlush(var rc: TRangeEnc);
var i: Integer;
begin for i:=0 to 4 do RCShiftLow(rc); end;

// ===========================================================================
// Range Decoder
// ===========================================================================

type
  TRangeDec = record Range, Code: LongWord; InStream: TStream; end;

function RCDecInit(var rc: TRangeDec; InStr: TStream): Boolean;
var b: Byte; i: Integer;
begin
  rc.InStream:=InStr;
  b:=InStr.ReadByte;
  if b<>$00 then begin Result:=False; Exit; end;
  rc.Code:=0; rc.Range:=$FFFFFFFF;
  for i:=0 to 3 do begin b:=InStr.ReadByte; rc.Code:=(rc.Code shl 8) or b; end;
  Result:=True;
end;

procedure RCDecNormalize(var rc: TRangeDec);
var b: Byte;
begin
  if rc.Range<RC_TOP_VALUE then begin
    rc.Range:=rc.Range shl 8;
    b:=0; rc.InStream.Read(b,1); // Read() returns 0 on EOF without exception; b stays 0
    rc.Code:=(rc.Code shl 8) or b;
  end;
end;

function RCDecBit(var rc: TRangeDec; var prob: TProb): Integer;
var bound: LongWord;
begin
  RCDecNormalize(rc);
  bound:=(rc.Range shr RC_BIT_MODEL_TOTAL_BITS)*prob;
  if rc.Code<bound then begin
    rc.Range:=bound; prob:=prob+((RC_BIT_MODEL_TOTAL-prob) shr RC_MOVE_BITS); Result:=0;
  end else begin
    rc.Code:=rc.Code-bound; rc.Range:=rc.Range-bound; prob:=prob-(prob shr RC_MOVE_BITS); Result:=1;
  end;
end;

function RCDecBitTree(var rc: TRangeDec; probs: PWord; numBits: Integer): LongWord;
var i: Integer; sym: LongWord;
begin
  sym:=1;
  for i:=0 to numBits-1 do sym:=(sym shl 1) or LongWord(RCDecBit(rc, probs[sym]));
  Result:=sym-(1 shl numBits);
end;

function RCDecBitTreeRev(var rc: TRangeDec; probs: PWord; numBits: Integer): LongWord;
var i: Integer; sym, bit: LongWord;
begin
  sym:=1; Result:=0;
  for i:=0 to numBits-1 do begin
    bit:=LongWord(RCDecBit(rc, probs[sym])); sym:=(sym shl 1) or bit; Result:=Result or (bit shl i);
  end;
end;

function RCDecDirect(var rc: TRangeDec; numBits: Integer): LongWord;
var i: Integer;
begin
  Result:=0;
  for i:=numBits-1 downto 0 do begin
    RCDecNormalize(rc); rc.Range:=rc.Range shr 1;
    if rc.Code>=rc.Range then begin rc.Code:=rc.Code-rc.Range; Result:=Result or (1 shl i); end;
  end;
end;

// ===========================================================================
// LZMA state transitions
// ===========================================================================

function StateIsLiteral(s: Integer): Boolean; begin Result:=s<7; end;
function StateAfterLit(s: Integer): Integer;
const T: array[0..11] of Integer=(0,0,0,0,1,2,3,4,5,6,4,5);
begin Result:=T[s]; end;
function StateAfterMatch(s: Integer): Integer;
begin if s<7 then Result:=7 else Result:=10; end;
function StateAfterLongRep(s: Integer): Integer;
begin if s<7 then Result:=8 else Result:=11; end;
function StateAfterShortRep(s: Integer): Integer;
begin if s<7 then Result:=9 else Result:=11; end;

// ===========================================================================
// LZ Dictionary
// ===========================================================================

type
  TLZDict = record
    Buf: PByte; Pos, Full, Limit, Size, DictSize: LongWord; HasWrapped: Boolean;
  end;

procedure DictAlloc(var d: TLZDict; dictSize: LongWord);
var alloc: LongWord;
begin
  if dictSize<4096 then dictSize:=4096;
  dictSize:=(dictSize+15) and not LongWord(15);
  d.DictSize:=dictSize; alloc:=dictSize+2*LZ_DICT_REPEAT_MAX;
  d.Size:=alloc; GetMem(d.Buf, alloc+32); FillChar(d.Buf^, alloc+32, 0);
end;

procedure DictFree(var d: TLZDict);
begin if d.Buf<>nil then begin FreeMem(d.Buf); d.Buf:=nil; end; end;

procedure DictReset(var d: TLZDict);
begin d.Pos:=LZ_DICT_INIT_POS; d.Full:=0; d.HasWrapped:=False;
  if d.Buf<>nil then d.Buf[LZ_DICT_INIT_POS-1]:=0; end;

function DictGet(const d: TLZDict; dist: LongWord): Byte;
var back: LongWord;
begin
  if dist<d.Pos then back:=d.Pos-dist-1
  else back:=d.Pos-dist-1+d.Size-LZ_DICT_REPEAT_MAX;
  Result:=d.Buf[back];
end;

procedure DictPut(var d: TLZDict; b: Byte);
begin d.Buf[d.Pos]:=b; Inc(d.Pos); if not d.HasWrapped then d.Full:=d.Pos-LZ_DICT_INIT_POS; end;

procedure DictRepeat(var d: TLZDict; dist, len: LongWord);
var back: LongWord;
begin
  if dist<d.Pos then back:=d.Pos-dist-1 else back:=d.Pos-dist-1+d.Size-LZ_DICT_REPEAT_MAX;
  while len>0 do begin d.Buf[d.Pos]:=d.Buf[back]; Inc(d.Pos); Inc(back); Dec(len); end;
  if not d.HasWrapped then d.Full:=d.Pos-LZ_DICT_INIT_POS;
end;

// ===========================================================================
// LZMA probability arrays
// ===========================================================================

type
  TLZMAProbs = record
    IsMatch:    array[0..LZMA_NUM_STATES*16-1] of TProb;
    IsRep:      array[0..LZMA_NUM_STATES-1] of TProb;
    IsRep0:     array[0..LZMA_NUM_STATES-1] of TProb;
    IsRep0Long: array[0..LZMA_NUM_STATES*16-1] of TProb;
    IsRep1:     array[0..LZMA_NUM_STATES-1] of TProb;
    IsRep2:     array[0..LZMA_NUM_STATES-1] of TProb;
    DistSlotArr:array[0..DIST_STATES*DIST_SLOTS-1] of TProb;
    DistSpecial:array[0..FULL_DISTANCES-DIST_MODEL_END-1] of TProb;
    DistAlign:  array[0..ALIGN_SIZE-1] of TProb;
    LenChoice:  array[0..1] of TProb;
    LenLow:     array[0..16*LEN_LOW_SYMS-1] of TProb;
    LenMid:     array[0..16*LEN_MID_SYMS-1] of TProb;
    LenHigh:    array[0..LEN_HIGH_SYMS-1] of TProb;
    RepChoice:  array[0..1] of TProb;
    RepLow:     array[0..16*LEN_LOW_SYMS-1] of TProb;
    RepMid:     array[0..16*LEN_MID_SYMS-1] of TProb;
    RepHigh:    array[0..LEN_HIGH_SYMS-1] of TProb;
    Literal:    array[0..LITERAL_CODER_SIZE*16-1] of TProb;
  end;
  PLZMAProbs = ^TLZMAProbs;

procedure InitProbArr(p: PWord; n: Integer);
var i: Integer; begin for i:=0 to n-1 do p[i]:=PROB_INIT_VAL; end;

procedure LZMAProbsInit(var p: TLZMAProbs; lc, lp: Integer);
begin
  InitProbArr(@p.IsMatch[0],Length(p.IsMatch));
  InitProbArr(@p.IsRep[0],Length(p.IsRep));
  InitProbArr(@p.IsRep0[0],Length(p.IsRep0));
  InitProbArr(@p.IsRep0Long[0],Length(p.IsRep0Long));
  InitProbArr(@p.IsRep1[0],Length(p.IsRep1));
  InitProbArr(@p.IsRep2[0],Length(p.IsRep2));
  InitProbArr(@p.DistSlotArr[0],Length(p.DistSlotArr));
  InitProbArr(@p.DistSpecial[0],Length(p.DistSpecial));
  InitProbArr(@p.DistAlign[0],Length(p.DistAlign));
  InitProbArr(@p.LenChoice[0],Length(p.LenChoice));
  InitProbArr(@p.LenLow[0],Length(p.LenLow));
  InitProbArr(@p.LenMid[0],Length(p.LenMid));
  InitProbArr(@p.LenHigh[0],Length(p.LenHigh));
  InitProbArr(@p.RepChoice[0],Length(p.RepChoice));
  InitProbArr(@p.RepLow[0],Length(p.RepLow));
  InitProbArr(@p.RepMid[0],Length(p.RepMid));
  InitProbArr(@p.RepHigh[0],Length(p.RepHigh));
  InitProbArr(@p.Literal[0],LITERAL_CODER_SIZE*(1 shl (lc+lp)));
end;

// ===========================================================================
// Length encode/decode
// ===========================================================================

function DecodeLen(var rc: TRangeDec; choice, low, mid, high: PWord;
                   posState: LongWord): LongWord;
begin
  if RCDecBit(rc,choice[0])=0 then
    Result:=RCDecBitTree(rc,@low[posState shl LEN_LOW_BITS],LEN_LOW_BITS)
  else if RCDecBit(rc,choice[1])=0 then
    Result:=LEN_LOW_SYMS+RCDecBitTree(rc,@mid[posState shl LEN_MID_BITS],LEN_MID_BITS)
  else
    Result:=LEN_LOW_SYMS+LEN_MID_SYMS+RCDecBitTree(rc,high,LEN_HIGH_BITS);
end;

procedure EncodeLen(var rc: TRangeEnc; choice, low, mid, high: PWord;
                    posState, len: LongWord);
begin
  Dec(len, MATCH_LEN_MIN);
  if len<LEN_LOW_SYMS then begin
    RCEncBit(rc,choice[0],0); RCEncBitTree(rc,@low[posState shl LEN_LOW_BITS],LEN_LOW_BITS,len);
  end else begin
    RCEncBit(rc,choice[0],1); Dec(len,LEN_LOW_SYMS);
    if len<LEN_MID_SYMS then begin
      RCEncBit(rc,choice[1],0); RCEncBitTree(rc,@mid[posState shl LEN_MID_BITS],LEN_MID_BITS,len);
    end else begin
      RCEncBit(rc,choice[1],1); Dec(len,LEN_MID_SYMS);
      RCEncBitTree(rc,high,LEN_HIGH_BITS,len);
    end;
  end;
end;

// ===========================================================================
// Distance decode/encode
// ===========================================================================

function DecodeDist(var rc: TRangeDec; var p: TLZMAProbs; lenState: LongWord): LongWord;
var slot, footerBits, base: LongWord;
begin
  slot:=RCDecBitTree(rc,@p.DistSlotArr[lenState shl DIST_SLOT_BITS],DIST_SLOT_BITS);
  if slot<DIST_MODEL_START then begin Result:=slot; Exit; end;
  footerBits:=(slot shr 1)-1; base:=(2 or (slot and 1)) shl footerBits;
  if slot<DIST_MODEL_END then
    Result:=base+RCDecBitTreeRev(rc,@p.DistSpecial[base-slot-1],footerBits)
  else begin
    Result:=base+(RCDecDirect(rc,footerBits-ALIGN_BITS) shl ALIGN_BITS);
    Result:=Result+RCDecBitTreeRev(rc,@p.DistAlign[0],ALIGN_BITS);
  end;
end;

procedure EncodeDist(var rc: TRangeEnc; var p: TLZMAProbs; dist, lenState: LongWord);
var slot, footerBits, base: LongWord;
begin
  slot:=DistSlot(dist);
  RCEncBitTree(rc,@p.DistSlotArr[lenState shl DIST_SLOT_BITS],DIST_SLOT_BITS,slot);
  if slot<DIST_MODEL_START then Exit;
  footerBits:=(slot shr 1)-1; base:=(2 or (slot and 1)) shl footerBits;
  if slot<DIST_MODEL_END then
    RCEncBitTreeRev(rc,@p.DistSpecial[base-slot-1],footerBits,dist-base)
  else begin
    RCEncDirect(rc,(dist-base) shr ALIGN_BITS,footerBits-ALIGN_BITS);
    RCEncBitTreeRev(rc,@p.DistAlign[0],ALIGN_BITS,dist and ALIGN_MASK);
  end;
end;

// ===========================================================================
// LZMA Decoder core
// ===========================================================================

type
  TLZMADecState = record
    rc: TRangeDec; dict: TLZDict; probs: TLZMAProbs;
    state: Integer; rep: array[0..3] of LongWord;
    lc, lp, pb: Integer; posMask, litPosMask: LongWord;
  end;

function LZMADecSymbol(var d: TLZMADecState): Boolean;
var
  posState, litIdx, sub: LongWord; matchB, sym, bit, mbit, len, lenState, tmp: LongWord;
begin
  Result:=True;
  posState:=(d.dict.Pos-LZ_DICT_INIT_POS) and d.posMask;
  if RCDecBit(d.rc,d.probs.IsMatch[d.state shl 4+posState])=0 then begin
    litIdx:=((d.dict.Pos-LZ_DICT_INIT_POS) and d.litPosMask) shl d.lc;
    if d.dict.Full>0 then litIdx:=litIdx+(DictGet(d.dict,0) shr (8-d.lc));
    sub:=litIdx*LITERAL_CODER_SIZE;
    if StateIsLiteral(d.state) then
      sym:=RCDecBitTree(d.rc,@d.probs.Literal[sub],8)
    else begin
      matchB:=LongWord(DictGet(d.dict,d.rep[0])); sym:=1;
      while sym<$100 do begin
        mbit:=(matchB shr 7) and 1; matchB:=matchB shl 1;
        bit:=LongWord(RCDecBit(d.rc,d.probs.Literal[sub+$100+(mbit shl 8)+sym]));
        sym:=(sym shl 1) or bit;
        if mbit<>bit then begin
          while sym<$100 do begin
            bit:=LongWord(RCDecBit(d.rc,d.probs.Literal[sub+sym]));
            sym:=(sym shl 1) or bit;
          end; break;
        end;
      end;
      sym:=sym and $FF;
    end;
    DictPut(d.dict,Byte(sym)); d.state:=StateAfterLit(d.state);
  end else begin
    if RCDecBit(d.rc,d.probs.IsRep[d.state])=0 then begin
      len:=DecodeLen(d.rc,@d.probs.LenChoice[0],@d.probs.LenLow[0],@d.probs.LenMid[0],
                     @d.probs.LenHigh[0],posState)+MATCH_LEN_MIN;
      d.state:=StateAfterMatch(d.state);
      if len-MATCH_LEN_MIN<DIST_STATES then lenState:=len-MATCH_LEN_MIN else lenState:=DIST_STATES-1;
      tmp:=DecodeDist(d.rc,d.probs,lenState);
      if tmp=$FFFFFFFF then begin Result:=False; Exit; end;
      d.rep[3]:=d.rep[2]; d.rep[2]:=d.rep[1]; d.rep[1]:=d.rep[0]; d.rep[0]:=tmp;
    end else begin
      if RCDecBit(d.rc,d.probs.IsRep0[d.state])=0 then begin
        if RCDecBit(d.rc,d.probs.IsRep0Long[d.state shl 4+posState])=0 then begin
          d.state:=StateAfterShortRep(d.state); DictPut(d.dict,DictGet(d.dict,d.rep[0])); Exit;
        end;
      end else begin
        if RCDecBit(d.rc,d.probs.IsRep1[d.state])=0 then begin
          tmp:=d.rep[1]; d.rep[1]:=d.rep[0]; d.rep[0]:=tmp;
        end else if RCDecBit(d.rc,d.probs.IsRep2[d.state])=0 then begin
          tmp:=d.rep[2]; d.rep[2]:=d.rep[1]; d.rep[1]:=d.rep[0]; d.rep[0]:=tmp;
        end else begin
          tmp:=d.rep[3]; d.rep[3]:=d.rep[2]; d.rep[2]:=d.rep[1]; d.rep[1]:=d.rep[0]; d.rep[0]:=tmp;
        end;
      end;
      len:=DecodeLen(d.rc,@d.probs.RepChoice[0],@d.probs.RepLow[0],@d.probs.RepMid[0],
                     @d.probs.RepHigh[0],posState)+MATCH_LEN_MIN;
      d.state:=StateAfterLongRep(d.state);
    end;
    DictRepeat(d.dict,d.rep[0],len);
  end;
end;

// ===========================================================================
// LZMA properties decode
// ===========================================================================

procedure DecodeLZMAProps(b: Byte; out lc, lp, pb: Integer);
var v: Integer;
begin
  if b>224 then raise ELZMAError.Create('Invalid LZMA props byte');
  pb:=b div 45; 
  v:=b-pb*45; 
  lp:=v div 9; 
  lc:=v mod 9;
end;

// ===========================================================================
// Limited-size stream wrapper
// ===========================================================================

type
  TLimitedStream = class(TStream)
  private FSrc: TStream; FLeft: Int64;
  public
    constructor Create(Src: TStream; Limit: Int64);
    function Read(var Buffer; Count: Longint): Longint; override;
    function Write(const Buffer; Count: Longint): Longint; override;
    function Seek(const Offset: Int64; Origin: TSeekOrigin): Int64; override;
  end;

constructor TLimitedStream.Create(Src: TStream; Limit: Int64);
begin 
  inherited Create; 
  FSrc:=Src; 
  FLeft:=Limit; 
end;

function TLimitedStream.Read(var Buffer; Count: Longint): Longint;
begin
  if Count>FLeft then Count:=FLeft;
  if Count=0 then 
  begin 
    Result:=0; 
    Exit; 
  end;
  Result:=FSrc.Read(Buffer,Count);  
  Dec(FLeft,Result);
end;

function TLimitedStream.Write(const Buffer; Count: Longint): Longint;
begin 
  Result:=0; 
  raise ELZMAError.Create('TLimitedStream: read-only'); 
end;

function TLimitedStream.Seek(const Offset: Int64; Origin: TSeekOrigin): Int64;
begin 
  Result:=0; 
  raise ELZMAError.Create('TLimitedStream: no seek'); 
end;

// ===========================================================================
// LZMA1 decode to output stream
// ===========================================================================

procedure LZMADecodeStream(InStr, OutStr: TStream; lc, lp, pb: Integer;
                            dictSize: LongWord; uncompSize: Int64);
var d: TLZMADecState; eopm: Boolean; ds, nOut: LongWord;
begin
  FillChar(d,SizeOf(d),0);
  d.lc:=lc; d.lp:=lp; d.pb:=pb;
  d.posMask:=(1 shl pb)-1; d.litPosMask:=(1 shl lp)-1;
  DictAlloc(d.dict,dictSize); DictReset(d.dict);
  LZMAProbsInit(d.probs,lc,lp);
  if not RCDecInit(d.rc,InStr) then raise ELZMAError.Create('LZMA: bad range coder init');
  d.dict.Limit:=d.dict.Size; ds:=d.dict.Pos; eopm:=False;
  while not eopm do begin
    if d.dict.Pos+MATCH_LEN_MAX>d.dict.Size then begin
      nOut:=d.dict.Pos-ds;
      if nOut>0 then begin OutStr.Write(d.dict.Buf[ds],nOut); if uncompSize>=0 then Dec(uncompSize,nOut); end;
      if uncompSize=0 then Break;
      Move(d.dict.Buf[d.dict.Pos-LZ_DICT_REPEAT_MAX],d.dict.Buf[0],LZ_DICT_REPEAT_MAX);
      d.dict.Pos:=LZ_DICT_REPEAT_MAX; d.dict.HasWrapped:=True; d.dict.Limit:=d.dict.Size; ds:=d.dict.Pos;
    end;
    if not LZMADecSymbol(d) then begin eopm:=True; Break; end;
    if (uncompSize>=0) and (Int64(d.dict.Pos-ds)>=uncompSize) then begin
      d.dict.Pos:=ds+LongWord(uncompSize); Break;
    end;
  end;
  nOut:=d.dict.Pos-ds;
  if nOut>0 then OutStr.Write(d.dict.Buf[ds],nOut);
  DictFree(d.dict);
end;

// ===========================================================================
// Match Finder — unified HC3/HC4/BT2/BT3/BT4
// ===========================================================================

const MF_EMPTY = LongWord($FFFFFFFF);

type
  TMatchFinder = record
    Kind: TMatchFinderKind;
    Buf: PByte; BufSize: LongWord;
    CyclicMask: LongWord;
    Pos: LongWord;
    Hash: PCardinal; Son: PCardinal;
    NiceLen, MaxDepth: Integer;
  end;

function MFHashVal(const mf: TMatchFinder): LongWord; inline;
var cur: PByte;
begin
  cur := mf.Buf + mf.Pos;
  case mf.Kind of
    mfkBT2:
      Result := LongWord(cur[0]) or (LongWord(cur[1]) shl 8);
    mfkHC3, mfkBT3:
      Result := (CRCTable[cur[0]] xor cur[1] xor (LongWord(cur[2]) shl 8)) and $FFFF;
  else // HC4, BT4
    Result := (CRCTable[cur[0]] xor cur[1] xor (LongWord(cur[2]) shl 8)
               xor (CRCTable[cur[3]] shl 5)) and $FFFFF;
  end;
end;

function MFMinBytes(kind: TMatchFinderKind): Integer; inline;
begin
  case kind of
    mfkBT2:        Result:=2; 
    mfkHC3,mfkBT3: Result:=3;
  else Result:=4;
  end;
end;

procedure MFInit(var mf: TMatchFinder; buf: PByte; bufSize, dictSize: LongWord;
                  kind: TMatchFinderKind; niceLen, maxDepth: Integer);
var cyclicSize, hashSz, sonSz, v: LongWord;
begin
  mf.Kind:=kind; mf.Buf:=buf; mf.BufSize:=bufSize;
  mf.NiceLen:=niceLen; mf.MaxDepth:=maxDepth; mf.Pos:=0;
  // CyclicSize = next power of 2 >= min(bufSize, dictSize)
  v:=dictSize; 
  if bufSize<v then v:=bufSize; 
  if v<1 then v:=1;
  cyclicSize:=1; 
  while cyclicSize<v do cyclicSize:=cyclicSize shl 1;
  mf.CyclicMask:=cyclicSize-1;
  case kind of
    mfkBT2,mfkHC3,mfkBT3: hashSz:=65536;
  else hashSz:=1048576;
  end;
  GetMem(mf.Hash, hashSz*SizeOf(LongWord));
  FillChar(mf.Hash^, hashSz*SizeOf(LongWord), $FF);
  case kind of
    mfkHC3,mfkHC4: sonSz:=cyclicSize;
  else sonSz:=cyclicSize*2;
  end;
  GetMem(mf.Son, sonSz*SizeOf(LongWord));
  FillChar(mf.Son^, sonSz*SizeOf(LongWord), $FF);
end;

procedure MFFree(var mf: TMatchFinder);
begin
  if mf.Hash<>nil then 
  begin 
    FreeMem(mf.Hash); 
    mf.Hash:=nil; 
  end;
  if mf.Son<>nil then 
  begin 
    FreeMem(mf.Son); 
    mf.Son:=nil; 
  end;
end;

// HC find+insert at mf.Pos; returns best (len, dist-1)
procedure HCFindInsert(var mf: TMatchFinder; hv: LongWord;
                        out bestLen: Integer; out bestDist: LongWord);
var curMatch, delta, cp: LongWord; cur, cand: PByte; mlen, maxLen, depth: Integer;
begin
  cp:=mf.Pos and mf.CyclicMask; cur:=mf.Buf+mf.Pos;
  maxLen:=mf.NiceLen;
  if mf.Pos+LongWord(maxLen)>mf.BufSize then maxLen:=Integer(mf.BufSize-mf.Pos);
  curMatch:=mf.Hash[hv]; mf.Hash[hv]:=mf.Pos; mf.Son[cp]:=curMatch;
  bestLen:=1; bestDist:=0; depth:=mf.MaxDepth;
  while (curMatch<>MF_EMPTY) and (depth>0) do begin
    Dec(depth); delta:=mf.Pos-curMatch;
    if delta>mf.CyclicMask+1 then Break;
    cand:=mf.Buf+curMatch; mlen:=0;
    while (mlen<maxLen) and (cand[mlen]=cur[mlen]) do Inc(mlen);
    if mlen>bestLen then begin bestLen:=mlen; bestDist:=delta-1; if mlen=maxLen then Break; end;
    curMatch:=mf.Son[curMatch and mf.CyclicMask];
  end;
end;

// BT find+insert at mf.Pos (tree update)
procedure BTFindInsert(var mf: TMatchFinder; hv: LongWord;
                        out bestLen: Integer; out bestDist: LongWord);
var
  curMatch, delta, cp, cp2, pairIdx, ptr0, ptr1: LongWord;
  cur, cand: PByte; mlen, maxLen, depth, len0, len1: Integer;
begin
  cp:=mf.Pos and mf.CyclicMask; cur:=mf.Buf+mf.Pos;
  maxLen:=mf.NiceLen;
  if mf.Pos+LongWord(maxLen)>mf.BufSize then maxLen:=Integer(mf.BufSize-mf.Pos);
  curMatch:=mf.Hash[hv]; mf.Hash[hv]:=mf.Pos;
  ptr1:=cp*2; ptr0:=cp*2+1;
  bestLen:=1; bestDist:=0; len0:=0; len1:=0; depth:=mf.MaxDepth;
  while True do begin
    if (curMatch=MF_EMPTY) or (depth=0) then begin
      mf.Son[ptr0]:=MF_EMPTY; mf.Son[ptr1]:=MF_EMPTY; Break;
    end;
    Dec(depth);
    delta:=mf.Pos-curMatch;
    if delta>mf.CyclicMask+1 then begin
      mf.Son[ptr0]:=MF_EMPTY; mf.Son[ptr1]:=MF_EMPTY; Break;
    end;
    cp2:=(cp-delta) and mf.CyclicMask; pairIdx:=cp2*2;
    cand:=mf.Buf+curMatch;
    mlen:=len0; if len1<mlen then mlen:=len1;
    while (mlen<maxLen) and (cand[mlen]=cur[mlen]) do Inc(mlen);
    if mlen>bestLen then begin bestLen:=mlen; bestDist:=delta-1; end;
    if mlen=maxLen then begin
      mf.Son[ptr1]:=mf.Son[pairIdx]; mf.Son[ptr0]:=mf.Son[pairIdx+1]; Break;
    end;
    if cand[mlen]<cur[mlen] then begin
      mf.Son[ptr1]:=curMatch; ptr1:=pairIdx+1; curMatch:=mf.Son[ptr1]; len1:=mlen;
    end else begin
      mf.Son[ptr0]:=curMatch; ptr0:=pairIdx;   curMatch:=mf.Son[ptr0]; len0:=mlen;
    end;
  end;
end;

// Find best match at current Pos, advance Pos
procedure MFFind(var mf: TMatchFinder; out bestLen: Integer; out bestDist: LongWord);
var hv: LongWord;
begin
  bestLen:=0; bestDist:=0;
  if mf.Pos+LongWord(MFMinBytes(mf.Kind))>mf.BufSize then begin Inc(mf.Pos); Exit; end;
  hv:=MFHashVal(mf);
  case mf.Kind of
    mfkHC3, mfkHC4: HCFindInsert(mf, hv, bestLen, bestDist);
  else               BTFindInsert(mf, hv, bestLen, bestDist);
  end;
  Inc(mf.Pos);
end;

// Update structures for skipped positions (during match copy)
procedure MFSkip(var mf: TMatchFinder; count: LongWord);
var hv, cp: LongWord;
begin
  while count>0 do begin
    Dec(count);
    if mf.Pos+LongWord(MFMinBytes(mf.Kind))<=mf.BufSize then begin
      hv:=MFHashVal(mf); cp:=mf.Pos and mf.CyclicMask;
      case mf.Kind of
        mfkHC3,mfkHC4: begin mf.Son[cp]:=mf.Hash[hv]; mf.Hash[hv]:=mf.Pos; end;
      else
        // BT: insert pos as leaf (no children); slight quality loss vs full tree update
        mf.Son[cp*2]:=MF_EMPTY; mf.Son[cp*2+1]:=MF_EMPTY;
        mf.Hash[hv]:=mf.Pos;
      end;
    end;
    Inc(mf.Pos);
  end;
end;

// ===========================================================================
// LZMA1 Encoder
// ===========================================================================

procedure LZMA1EncodeRaw(buf: PByte; size: LongWord; lc, lp, pb: Integer;
                          niceLen, maxDepth: Integer; mfKind: TMatchFinderKind;
                          OutStr: TStream);
var
  rc: TRangeEnc; probs: TLZMAProbs; state: Integer; rep: array[0..3] of LongWord;
  posMask, litPosMask: LongWord; mf: TMatchFinder; pos, posState, lenState: LongWord;
  litIdx, sub, sym, bit, mbit, tmp: LongWord; litByte, prevByte, matchByte: Byte;
  mlen: Integer; mdist: LongWord; isRep: Boolean;
begin
  posMask:=(1 shl pb)-1; litPosMask:=(1 shl lp)-1;
  state:=0; rep[0]:=0; rep[1]:=0; rep[2]:=0; rep[3]:=0;
  LZMAProbsInit(probs,lc,lp); RCEncInit(rc,OutStr);
  MFInit(mf, buf, size, size, mfKind, niceLen, maxDepth);
  pos:=0;
  while pos<size do begin
    posState:=pos and posMask;
    mlen:=0; mdist:=0;
    MFFind(mf, mlen, mdist);
    if mlen<MATCH_LEN_MIN then begin
      RCEncBit(rc,probs.IsMatch[state shl 4+posState],0);
      litByte:=buf[pos]; if pos>0 then prevByte:=buf[pos-1] else prevByte:=0;
      litIdx:=(pos and litPosMask) shl lc; litIdx:=litIdx or (prevByte shr (8-lc));
      sub:=litIdx*LITERAL_CODER_SIZE;
      if StateIsLiteral(state) then
        RCEncBitTree(rc,@probs.Literal[sub],8,litByte)
      else begin
        if pos>rep[0] then matchByte:=buf[pos-1-rep[0]] else matchByte:=0;
        sym:=1;
        while sym<$100 do begin
          mbit:=(LongWord(matchByte) shr 7) and 1; matchByte:=matchByte shl 1;
          bit:=(LongWord(litByte) shr 7) and 1; litByte:=litByte shl 1;
          RCEncBit(rc,probs.Literal[sub+$100+(mbit shl 8)+sym],bit);
          sym:=(sym shl 1) or bit;
          if mbit<>bit then begin
            while sym<$100 do begin
              bit:=(LongWord(litByte) shr 7) and 1; litByte:=litByte shl 1;
              RCEncBit(rc,probs.Literal[sub+sym],bit); sym:=(sym shl 1) or bit;
            end; break;
          end;
        end;
      end;
      state:=StateAfterLit(state); Inc(pos);
    end else begin
      // Check rep distances
      isRep:=False;
      if mdist=rep[0] then begin
        RCEncBit(rc,probs.IsMatch[state shl 4+posState],1);
        RCEncBit(rc,probs.IsRep[state],1); RCEncBit(rc,probs.IsRep0[state],0);
        isRep:=True;
        if mlen=1 then begin RCEncBit(rc,probs.IsRep0Long[state shl 4+posState],0); state:=StateAfterShortRep(state);
        end else begin
          RCEncBit(rc,probs.IsRep0Long[state shl 4+posState],1);
          EncodeLen(rc,@probs.RepChoice[0],@probs.RepLow[0],@probs.RepMid[0],@probs.RepHigh[0],posState,mlen);
          state:=StateAfterLongRep(state);
        end;
      end else if mdist=rep[1] then begin
        RCEncBit(rc,probs.IsMatch[state shl 4+posState],1);
        RCEncBit(rc,probs.IsRep[state],1); RCEncBit(rc,probs.IsRep0[state],1); RCEncBit(rc,probs.IsRep1[state],0);
        isRep:=True; tmp:=rep[1]; rep[1]:=rep[0]; rep[0]:=tmp;
        EncodeLen(rc,@probs.RepChoice[0],@probs.RepLow[0],@probs.RepMid[0],@probs.RepHigh[0],posState,mlen);
        state:=StateAfterLongRep(state);
      end else if mdist=rep[2] then begin
        RCEncBit(rc,probs.IsMatch[state shl 4+posState],1);
        RCEncBit(rc,probs.IsRep[state],1); RCEncBit(rc,probs.IsRep0[state],1);
        RCEncBit(rc,probs.IsRep1[state],1); RCEncBit(rc,probs.IsRep2[state],0);
        isRep:=True; tmp:=rep[2]; rep[2]:=rep[1]; rep[1]:=rep[0]; rep[0]:=tmp;
        EncodeLen(rc,@probs.RepChoice[0],@probs.RepLow[0],@probs.RepMid[0],@probs.RepHigh[0],posState,mlen);
        state:=StateAfterLongRep(state);
      end else if mdist=rep[3] then begin
        RCEncBit(rc,probs.IsMatch[state shl 4+posState],1);
        RCEncBit(rc,probs.IsRep[state],1); RCEncBit(rc,probs.IsRep0[state],1);
        RCEncBit(rc,probs.IsRep1[state],1); RCEncBit(rc,probs.IsRep2[state],1);
        isRep:=True; tmp:=rep[3]; rep[3]:=rep[2]; rep[2]:=rep[1]; rep[1]:=rep[0]; rep[0]:=tmp;
        EncodeLen(rc,@probs.RepChoice[0],@probs.RepLow[0],@probs.RepMid[0],@probs.RepHigh[0],posState,mlen);
        state:=StateAfterLongRep(state);
      end;
      if not isRep then begin
        RCEncBit(rc,probs.IsMatch[state shl 4+posState],1); RCEncBit(rc,probs.IsRep[state],0);
        EncodeLen(rc,@probs.LenChoice[0],@probs.LenLow[0],@probs.LenMid[0],@probs.LenHigh[0],posState,mlen);
        if LongWord(mlen-MATCH_LEN_MIN)<DIST_STATES then lenState:=LongWord(mlen-MATCH_LEN_MIN) else lenState:=DIST_STATES-1;
        EncodeDist(rc,probs,mdist,lenState);
        rep[3]:=rep[2]; rep[2]:=rep[1]; rep[1]:=rep[0]; rep[0]:=mdist;
        state:=StateAfterMatch(state);
      end;
      // Skip intermediate positions (no MFFind needed; slight quality loss for BT)
      if mlen>1 then MFSkip(mf, LongWord(mlen)-1);
      Inc(pos, LongWord(mlen));
    end;
  end;
  // EOPM
  posState:=pos and posMask;
  RCEncBit(rc,probs.IsMatch[state shl 4+posState],1); RCEncBit(rc,probs.IsRep[state],0);
  EncodeLen(rc,@probs.LenChoice[0],@probs.LenLow[0],@probs.LenMid[0],@probs.LenHigh[0],posState,MATCH_LEN_MIN);
  RCEncBitTree(rc,@probs.DistSlotArr[0],DIST_SLOT_BITS,63);
  RCEncDirect(rc,$03FFFFFF,26); RCEncBitTreeRev(rc,@probs.DistAlign[0],ALIGN_BITS,$F);
  RCEncFlush(rc); MFFree(mf);
end;

// ===========================================================================
// BCJ Filters
// ===========================================================================

// x86 BCJ (E8/E9 CALL/JMP)
function ImplBCJx86(buf: PByte; size: LongWord; isEncode: Boolean): LongWord;
const MASK_TO_BIT_NUMBER: array[0..4] of LongWord = (0,1,2,2,3);
var
  prevMask, prevPos, nowPos, offset: LongWord;
  i, j: LongWord; b: Byte; src, dest: LongWord; maskBitNum: LongWord;
begin
  prevMask:=0; prevPos:=LongWord($FFFFFFFB); // (uint32_t)(-5)
  i:=0;
  while i+5<=size do begin
    b:=buf[i];
    if (b<>$E8) and (b<>$E9) then begin Inc(i); continue; end;
    nowPos:=i;
    offset:=nowPos-prevPos;
    prevPos:=nowPos;
    if offset>5 then prevMask:=0
    else begin
      for j:=0 to offset-1 do begin prevMask:=prevMask and $77; prevMask:=prevMask shl 1; end;
    end;
    b:=buf[i+4];
    if ((b=0) or (b=$FF)) and ((prevMask shr 1)<=4) and ((prevMask shr 1)<>3) then begin
      src:=Read32LE(buf+i+1);
      repeat
        if isEncode then dest:=src+(nowPos+5) else dest:=src-(nowPos+5);
        if prevMask=0 then break;
        maskBitNum:=MASK_TO_BIT_NUMBER[prevMask shr 1];
        b:=Byte(dest shr (24-maskBitNum*8));
        if (b<>0) and (b<>$FF) then break;
        src:=dest xor ((1 shl (32-maskBitNum*8))-1);
      until False;
      buf[i+4]:=Byte(not (((dest shr 24) and 1)-1));
      buf[i+3]:=Byte(dest shr 16); buf[i+2]:=Byte(dest shr 8); buf[i+1]:=Byte(dest);
      Inc(i,5); prevMask:=0;
    end else begin
      Inc(i); prevMask:=prevMask or 1;
      if (b=0) or (b=$FF) then prevMask:=prevMask or $10;  // b still holds buf[old_i+4]
    end;
  end;
  Result:=i;
end;

// PowerPC BCJ (big-endian)
procedure ImplBCJppc(buf: PByte; size: LongWord; isEncode: Boolean);
var i: LongWord; instr, src, dest: LongWord;
begin
  i:=0;
  while i+4<=size do begin
    instr:=Read32BE(buf+i);
    if ((instr shr 26)=$12) and ((instr and 3)=1) then begin
      src:=(instr shr 2) and $FFFFFF;
      if isEncode then dest:=src+(i shr 2) else dest:=src-(i shr 2);
      instr:=(instr and $FC000003) or ((dest and $FFFFFF) shl 2);
      Write32BE(buf+i,instr);
    end;
    Inc(i,4);
  end;
end;

// ARM BCJ (little-endian, 4-byte aligned)
procedure ImplBCJarm(buf: PByte; size: LongWord; isEncode: Boolean);
var i: LongWord; src, dest: LongWord;
begin
  i:=0;
  while i+4<=size do begin
    if buf[i+3]=$EB then begin
      src:=(LongWord(buf[i+2]) shl 16) or (LongWord(buf[i+1]) shl 8) or buf[i];
      src:=src shl 2;
      if isEncode then dest:=i+8+src else dest:=src-(i+8);
      dest:=dest shr 2;
      buf[i]:=Byte(dest); buf[i+1]:=Byte(dest shr 8); buf[i+2]:=Byte(dest shr 16);
    end;
    Inc(i,4);
  end;
end;

// ARM Thumb BCJ
procedure ImplBCJarmthumb(buf: PByte; size: LongWord; isEncode: Boolean);
var i: LongWord; src, dest: LongWord;
begin
  i:=0;
  while i+4<=size do begin
    if ((buf[i+1] and $F8)=$F0) and ((buf[i+3] and $F8)=$F8) then begin
      src:=(LongWord(buf[i+1] and 7) shl 19) or (LongWord(buf[i]) shl 11) or
           (LongWord(buf[i+3] and 7) shl 8) or buf[i+2];
      if isEncode then dest:=(i+4)+(src shl 1) else dest:=(src shl 1)-i-4;
      dest:=dest shr 1;
      buf[i+1]:=$F0 or Byte((dest shr 19) and 7);
      buf[i]:=Byte(dest shr 11);
      buf[i+3]:=$F8 or Byte((dest shr 8) and 7);
      buf[i+2]:=Byte(dest);
      Inc(i,2);
    end;
    Inc(i,2);
  end;
end;

// SPARC BCJ (big-endian)
// Handles CALL (instr shr 22 = $100, byte[0]=$40) and
// BICC/FBICC (instr shr 22 = $1FF, byte[0]=$7F, byte[1] top 2 bits=$C0).
// Both patterns have bits[31:30]=01, so the same transform applies to each.
// Reference: XZ Utils liblzma/simple/sparc.c
procedure ImplBCJsparc(buf: PByte; size: LongWord; isEncode: Boolean);
var i: LongWord; src, dest, instr: LongWord;
begin
  i:=0;
  while i+4<=size do begin
    instr:=Read32BE(buf+i);
    if (instr shr 22 = $100) or (instr shr 22 = $1FF) then begin
      src:=(instr and $3FFFFFFF) shl 2;
      if isEncode then dest:=i+src else dest:=src-i;
      instr:=$40000000 or ((dest shr 2) and $3FFFFFFF);
      Write32BE(buf+i, instr);
    end;
    Inc(i,4);
  end;
end;

// ARM64 BCJ (little-endian, 4-byte aligned)
procedure ImplBCJarm64(buf: PByte; size: LongWord; isEncode: Boolean);
var i: LongWord; instr, src, dest, pc: LongWord;
begin
  i:=0;
  while i+4<=size do begin
    instr:=Read32LE(buf+i); pc:=i;
    if (instr shr 26)=$25 then begin
      // BL
      src:=instr and $03FFFFFF;
      if isEncode then begin
        // src is relative, convert to absolute
        dest:=(pc shr 2)+src; instr:=$94000000 or (dest and $03FFFFFF);
      end else begin
        dest:=src-(pc shr 2); instr:=$94000000 or (dest and $03FFFFFF);
      end;
      Write32LE(buf+i,instr);
    end else if (instr and $9F000000)=$90000000 then begin
      // ADRP — only +/-512 MiB range
      src:=((instr shr 29) and 3) or ((instr shr 3) and $001FFFFC);
      if ((src+$00020000) and $001C0000)<>0 then begin Inc(i,4); continue; end;
      instr:=instr and $9000001F; pc:=pc shr 12;
      if isEncode then dest:=src+pc else dest:=src-pc;
      instr:=instr or ((dest and 3) shl 29) or ((dest and $0003FFFC) shl 3)
             or ((LongWord(0)-(dest and $00020000)) and $00E00000);
      Write32LE(buf+i,instr);
    end;
    Inc(i,4);
  end;
end;

// Dispatch BCJ apply
procedure BCJApply(bcj: TBCJFilter; buf: PByte; size: LongWord; isEncode: Boolean);
begin
  case bcj of
    bcjX86:       ImplBCJx86(buf,size,isEncode);
    bcjPowerPC:   ImplBCJppc(buf,size,isEncode);
    bcjARM:       ImplBCJarm(buf,size,isEncode);
    bcjARMThumb:  ImplBCJarmthumb(buf,size,isEncode);
    bcjSPARC:     ImplBCJsparc(buf,size,isEncode);
    bcjARM64:     ImplBCJarm64(buf,size,isEncode);
    // bcjIA64: not implemented (very rare)
  end;
end;

function BCJFilterID(bcj: TBCJFilter): Byte;
begin
  case bcj of
    bcjX86:      Result:=$04;
    bcjPowerPC:  Result:=$05;
    bcjIA64:     Result:=$06; 
    bcjARM:      Result:=$07;
    bcjARMThumb: Result:=$08; 
    bcjSPARC:    Result:=$09;
    bcjARM64:    Result:=$0A;
  else           Result:=$04;
  end;
end;

function BCJFromID(id: Byte): TBCJFilter;
begin
  case id of
    $04: Result:=bcjX86;     
    $05: Result:=bcjPowerPC;
    $06: Result:=bcjIA64;
    $07: Result:=bcjARM;
    $08: Result:=bcjARMThumb;
    $09: Result:=bcjSPARC;
    $0A: Result:=bcjARM64;
  else Result:=bcjNone;
  end;
end;

// ===========================================================================
// Delta Filter
// ===========================================================================

procedure DeltaEncode(buf: PByte; size: LongWord; dist: Integer);
var i: LongWord;
begin
  if dist<1 then dist:=1;
  for i:=size-1 downto LongWord(dist) do
    buf[i]:=buf[i]-buf[i-LongWord(dist)];
end;

procedure DeltaDecode(buf: PByte; size: LongWord; dist: Integer);
var i: LongWord;
begin
  if dist<1 then dist:=1;
  for i:=LongWord(dist) to size-1 do
    buf[i]:=buf[i]+buf[i-LongWord(dist)];
end;

// ===========================================================================
// LZMA2 Encoder
// ===========================================================================

procedure LZMA2Encode(InBuf: PByte; InSize: LongWord; OutStr: TStream;
                       lc, lp, pb: Integer; mfKind: TMatchFinderKind;
                       niceLen, maxDepth: Integer);
var
  propsByte: Byte; chunkStart, uncompSize, compSize: LongWord;
  chunkMem: TMemoryStream; firstChunk: Boolean; ctrl: Byte;
begin
  propsByte:=Byte((pb*5+lp)*9+lc); 
  firstChunk:=True; 
  chunkStart:=0;

  while chunkStart<InSize do begin
    if InSize-chunkStart>LongWord(LZMA2_UNCOMPRESSED_MAX) then
      uncompSize:=LZMA2_UNCOMPRESSED_MAX else uncompSize:=InSize-chunkStart;
    chunkMem:=TMemoryStream.Create;
    try
      LZMA1EncodeRaw(InBuf+chunkStart, uncompSize, lc, lp, pb, niceLen, maxDepth, mfKind, chunkMem);
      compSize:=chunkMem.Size; // per XZ LZMA2 spec: props byte is NOT counted in Compressed Size
      if compSize<uncompSize then begin
        if firstChunk then ctrl:=$E0 or Byte(((uncompSize-1) shr 16) and $1F)
        else ctrl:=$C0 or Byte(((uncompSize-1) shr 16) and $1F);
        OutStr.WriteByte(ctrl);
        OutStr.WriteByte(Byte(((uncompSize-1) shr 8) and $FF));
        OutStr.WriteByte(Byte((uncompSize-1) and $FF));
        OutStr.WriteByte(Byte(((compSize-1) shr 8) and $FF));
        OutStr.WriteByte(Byte((compSize-1) and $FF));
        OutStr.WriteByte(propsByte);
        chunkMem.Position:=0; OutStr.CopyFrom(chunkMem, chunkMem.Size);
      end else begin
        if firstChunk then OutStr.WriteByte(1) else OutStr.WriteByte(2);
        OutStr.WriteByte(Byte(((uncompSize-1) shr 8) and $FF));
        OutStr.WriteByte(Byte((uncompSize-1) and $FF));
        OutStr.Write(InBuf[chunkStart], uncompSize);
      end;
      firstChunk:=False;
    finally chunkMem.Free; end;
    Inc(chunkStart, uncompSize);
  end;
  OutStr.WriteByte(0);
end;

// ===========================================================================
// LZMA2 Decoder
// ===========================================================================

procedure LZMA2Decode(const InStr, OutStr: TStream; dictSize: LongWord);
var
  ctrl, b: Byte; uncompSize, compSize, left, n: LongWord;
  needDictReset: Boolean; lc, lp, pb: Integer;
  dict: TLZDict; probs: TLZMAProbs; state: Integer; rep: array[0..3] of LongWord;
  posMask, litPosMask: LongWord; buf: array[0..4095] of Byte;
  limStr: TMemoryStream; chunk: TLZMADecState; ds, nOut: LongWord;
begin
  needDictReset:=True; 
  lc:=3; lp:=0; pb:=2;
  DictAlloc(dict,dictSize);
  DictReset(dict);
  FillChar(probs,SizeOf(probs),0); 
  state:=0;
  rep[0]:=0; rep[1]:=0; rep[2]:=0; rep[3]:=0;
  try
    while True do begin
      ctrl:=InStr.ReadByte;
      if ctrl=0 then Break;
      if (ctrl>=$E0) or (ctrl=1) then needDictReset:=True;
      if needDictReset then begin DictReset(dict); needDictReset:=False; end;
      if ctrl>=$80 then begin
        uncompSize:=(LongWord(ctrl) and $1F) shl 16;
        b:=InStr.ReadByte; uncompSize:=uncompSize or (LongWord(b) shl 8);
        b:=InStr.ReadByte; uncompSize:=uncompSize or LongWord(b); Inc(uncompSize);
        b:=InStr.ReadByte; compSize:=LongWord(b) shl 8;
        b:=InStr.ReadByte; compSize:=compSize or LongWord(b); Inc(compSize);
        if ctrl>=$C0 then
        begin
          b:=InStr.ReadByte; 
          DecodeLZMAProps(b,lc,lp,pb);
          posMask:=(1 shl pb)-1; 
          litPosMask:=(1 shl lp)-1;
          LZMAProbsInit(probs,lc,lp); 
          state:=0;
          rep[0]:=0; 
          rep[1]:=0; 
          rep[2]:=0; 
          rep[3]:=0;
          // NOTE: Properties byte is NOT counted in Compressed Size (per XZ LZMA2 spec)
        end else if ctrl>=$A0 then 
        begin
          LZMAProbsInit(probs,lc,lp);
          state:=0;
          rep[0]:=0; 
          rep[1]:=0; 
          rep[2]:=0;
          rep[3]:=0;
        end;
        FillChar(chunk,SizeOf(chunk),0);
        chunk.lc:=lc; 
        chunk.lp:=lp; 
        chunk.pb:=pb;
        chunk.posMask:=posMask; 
        chunk.litPosMask:=litPosMask;
        Move(dict,chunk.dict,SizeOf(TLZDict));
        Move(probs,chunk.probs,SizeOf(TLZMAProbs));
        chunk.state:=state;
        chunk.rep[0]:=rep[0]; chunk.rep[1]:=rep[1];
        chunk.rep[2]:=rep[2]; chunk.rep[3]:=rep[3];
        limStr:=TMemoryStream.Create;
        try
          limStr.CopyFrom(InStr,compSize); limStr.Position:=0;
          if not RCDecInit(chunk.rc,limStr) then raise ELZMAError.Create('LZMA2: bad range coder init');
          left:=uncompSize; 
          chunk.dict.Limit:=chunk.dict.Size; 
          ds:=chunk.dict.Pos;
          while left>0 do begin
            if chunk.dict.Pos+MATCH_LEN_MAX>chunk.dict.Size then begin
              nOut:=chunk.dict.Pos-ds;
              if nOut>0 then 
              begin 
                OutStr.Write(chunk.dict.Buf[ds],nOut); 
                Dec(left,nOut); 
              end;
              Move(chunk.dict.Buf[chunk.dict.Pos-LZ_DICT_REPEAT_MAX],chunk.dict.Buf[0],LZ_DICT_REPEAT_MAX);
              chunk.dict.Pos:=LZ_DICT_REPEAT_MAX; 
              chunk.dict.HasWrapped:=True;
              chunk.dict.Limit:=chunk.dict.Size; 
              ds:=chunk.dict.Pos;
              if left=0 then Break;
            end;
            if not LZMADecSymbol(chunk) then raise ELZMAError.Create('LZMA2: unexpected EOPM');
            if Int64(chunk.dict.Pos-ds)>=Int64(left) then 
            begin
              chunk.dict.Pos:=ds+left; 
              left:=0;
            end;
          end;
          nOut:=chunk.dict.Pos-ds;
          if nOut>0 then OutStr.Write(chunk.dict.Buf[ds],nOut);
        finally limStr.Free; end;
        Move(chunk.dict,dict,SizeOf(TLZDict));
        Move(chunk.probs,probs,SizeOf(TLZMAProbs));
        state:=chunk.state;
        rep[0]:=chunk.rep[0]; 
        rep[1]:=chunk.rep[1];
        rep[2]:=chunk.rep[2];
        rep[3]:=chunk.rep[3];
      end else begin
        if ctrl>2 then raise ELZMAError.Create('LZMA2: invalid control byte');
        b:=InStr.ReadByte; 
        compSize:=LongWord(b) shl 8;
        b:=InStr.ReadByte; 
        compSize:=compSize or LongWord(b); 
        Inc(compSize);
        left:=compSize;
        while left>0 do begin
          n:=left; if n>SizeOf(buf) then n:=SizeOf(buf);
          n:=InStr.Read(buf[0],n);
          if n=0 then raise ELZMAError.Create('LZMA2: truncated');
          OutStr.Write(buf[0],n); Dec(left,n);
        end;
      end;
    end;
  finally DictFree(dict); end;
end;

// ===========================================================================
// VLI encoding/decoding
// ===========================================================================

procedure WriteVLI(OutStr: TStream; value: Int64);
begin
  while value>$7F do 
  begin 
    OutStr.WriteByte(Byte(value and $7F) or $80); 
    value:=value shr 7; 
  end;
  OutStr.WriteByte(Byte(value));
end;

function VLIFromBuf(p: PByte; var off: Integer; maxOff: Integer): Int64;
var b: Byte; shift: Integer;
begin
  Result:=0; shift:=0;
  repeat
    if off>=maxOff then raise ELZMAError.Create('.xz: truncated VLI');
    b:=p[off]; Inc(off); Result:=Result or (Int64(b and $7F) shl shift); Inc(shift,7);
  until (b and $80)=0;
end;

// ===========================================================================
// .lzma container
// ===========================================================================

procedure LZMACompressStream(const InStr, OutStr: TStream);
const lc=3; lp=0; pb=2; dictSize=1 shl 23;
var ms: TMemoryStream; propsByte: Byte; i: Integer;
begin
  propsByte:=(pb*5+lp)*9+lc;
  ms:=TMemoryStream.Create;
  try
    ms.CopyFrom(InStr,0);
    OutStr.WriteByte(propsByte);
    OutStr.WriteByte(dictSize and $FF); 
    OutStr.WriteByte((dictSize shr 8) and $FF);
    OutStr.WriteByte((dictSize shr 16) and $FF); 
    OutStr.WriteByte((dictSize shr 24) and $FF);
    for i:=0 to 7 do OutStr.WriteByte($FF);
    LZMA1EncodeRaw(ms.Memory, ms.Size, lc, lp, pb, 64, 32, mfkHC4, OutStr);
  finally 
    ms.Free; 
  end;
end;

procedure LZMADecompressStream(const InStr, OutStr: TStream);
var hdr: array[0..12] of Byte; lc, lp, pb: Integer; dictSize: LongWord;
    uncompSize: Int64; i: Integer;
begin
  if InStr.Read(hdr[0],13)<>13 then raise ELZMAError.Create('.lzma: truncated header');
  DecodeLZMAProps(hdr[0],lc,lp,pb);
  dictSize:=LongWord(hdr[1]) or (LongWord(hdr[2]) shl 8) or
            (LongWord(hdr[3]) shl 16) or (LongWord(hdr[4]) shl 24);
  uncompSize:=0;
  for i:=0 to 7 do uncompSize:=uncompSize or (Int64(hdr[5+i]) shl (i*8));
  if uncompSize=Int64(-1) then uncompSize:=-1;
  LZMADecodeStream(InStr,OutStr,lc,lp,pb,dictSize,uncompSize);
end;

// ===========================================================================
// .xz container — helper to write block header
// ===========================================================================

procedure WriteBlockHeader(OutStr: TStream; dictSizeProp: Byte;
                            bcj: TBCJFilter; deltaDist: Integer;
                            out bHdrBytes: LongWord);
var bhMs: TMemoryStream; crc: LongWord; bHdrSize: LongWord; nFilters: Integer;
begin
  // Count filters: BCJ (opt) + Delta (opt) + LZMA2
  nFilters:=1;
  if bcj<>bcjNone then Inc(nFilters);
  if deltaDist>0 then Inc(nFilters);

  bhMs:=TMemoryStream.Create;
  try
    bhMs.WriteByte(0);                        // placeholder size byte
    bhMs.WriteByte(Byte(nFilters-1));         // flags: filter count - 1
    // Filters in order (BCJ first, then Delta, then LZMA2)
    if bcj<>bcjNone then begin
      WriteVLI(bhMs, BCJFilterID(bcj));       // filter ID
      WriteVLI(bhMs, 0);                      // props size = 0
    end;
    if deltaDist>0 then begin
      WriteVLI(bhMs, $03);                    // Delta filter ID
      WriteVLI(bhMs, 1);                      // props size = 1
      bhMs.WriteByte(Byte(deltaDist-1));      // delta distance - 1
    end;
    WriteVLI(bhMs, $21);                      // LZMA2 filter ID
    WriteVLI(bhMs, 1);                        // props size = 1
    bhMs.WriteByte(dictSizeProp);
    // Pad so that (bhMs.Size + 4) is multiple of 4
    while (bhMs.Size+4) mod 4 <> 0 do bhMs.WriteByte(0);
    bHdrSize:=bhMs.Size+4;
    PByte(bhMs.Memory)[0]:=Byte(bHdrSize div 4 - 1);  // spec: stored as (size/4)-1
    crc:=CRC32Update(0, PByte(bhMs.Memory), bhMs.Size);
    bhMs.WriteByte(crc and $FF); 
    bhMs.WriteByte((crc shr 8) and $FF);
    bhMs.WriteByte((crc shr 16) and $FF); 
    bhMs.WriteByte((crc shr 24) and $FF);
    bHdrBytes:=bhMs.Size;
    bhMs.Position:=0; 
    OutStr.CopyFrom(bhMs, bhMs.Size);
  finally bhMs.Free; end;
end;

function XZCheckSize(check: TXZCheckType): Integer;
begin
  case check of
    xzCRC32: Result:=4; 
    xzCRC64: Result:=8; 
    xzSHA256: Result:=32;
  else Result:=0;
  end;
end;

// ===========================================================================
// .xz Encoder
// ===========================================================================

procedure XZCompressEx(inBuf: PByte; inSize: LongWord; OutStr: TStream;
                        dictSizeProp: Byte; mfKind: TMatchFinderKind;
                        niceLen, maxDepth: Integer;
                        check: TXZCheckType; bcj: TBCJFilter; deltaDist: Integer);
var
  lc,lp,pb: Integer; bcjBuf: PByte; lzma2Ms, idxMs: TMemoryStream;
  packedSize, bHdrBytes: LongWord; crc: LongWord; tmp: array[0..5] of Byte;
  backwardSize, idxSize: LongWord;
  sha: TSHA256Digest; crc64: UInt64;
begin
  lc:=3; 
  lp:=0; 
  pb:=2;

  // Apply BCJ forward then Delta forward (in-place on copy of input)
  if (bcj<>bcjNone) or (deltaDist>0) then begin
    GetMem(bcjBuf, inSize);
    Move(inBuf^, bcjBuf^, inSize);
    if bcj<>bcjNone then BCJApply(bcj, bcjBuf, inSize, True);
    if deltaDist>0 then DeltaEncode(bcjBuf, inSize, deltaDist);
  end else
    bcjBuf:=inBuf;

  lzma2Ms:=TMemoryStream.Create;
  idxMs:=TMemoryStream.Create;
  try
    // LZMA2 encode (of possibly BCJ/Delta transformed data)
    LZMA2Encode(bcjBuf, inSize, lzma2Ms, lc, lp, pb, mfKind, niceLen, maxDepth);
    packedSize:=lzma2Ms.Size;

    // === Stream header ===
    OutStr.WriteByte($FD); OutStr.WriteByte($37); OutStr.WriteByte($7A);
    OutStr.WriteByte($58); OutStr.WriteByte($5A); OutStr.WriteByte($00);
    tmp[0]:=0; tmp[1]:=Byte(check);
    crc:=CRC32Update(0,@tmp[0],2);
    OutStr.Write(tmp[0],2);
    OutStr.WriteByte(crc and $FF); OutStr.WriteByte((crc shr 8) and $FF);
    OutStr.WriteByte((crc shr 16) and $FF); OutStr.WriteByte((crc shr 24) and $FF);

    // === Block header ===
    WriteBlockHeader(OutStr, dictSizeProp, bcj, deltaDist, bHdrBytes);

    // === Block data ===
    lzma2Ms.Position:=0; OutStr.CopyFrom(lzma2Ms, lzma2Ms.Size);

    // Pad block data to multiple of 4
    while packedSize mod 4 <> 0 do begin OutStr.WriteByte(0); Inc(packedSize); end;

    // === Block check (on original unfiltered input) ===
    case check of
      xzNone: ; // no check bytes
      xzCRC32: begin
        crc:=CRC32Update(0,inBuf,inSize);
        OutStr.WriteByte(crc and $FF); OutStr.WriteByte((crc shr 8) and $FF);
        OutStr.WriteByte((crc shr 16) and $FF); OutStr.WriteByte((crc shr 24) and $FF);
      end;
      xzCRC64: begin
        crc64:=CRC64Update(0,inBuf,inSize);
        OutStr.Write(crc64,8);
      end;
      xzSHA256: begin
        SHA256_Buf(inBuf,inSize,sha);
        OutStr.Write(sha[0],32);
      end;
    end;

    // === Index ===
    // Unpadded Size = Block Header + Compressed Data + Check  (no padding)
    idxMs.WriteByte(0);            // index indicator
    WriteVLI(idxMs,1);             // 1 record
    WriteVLI(idxMs, Int64(bHdrBytes) + Int64(lzma2Ms.Size) + XZCheckSize(check));
    WriteVLI(idxMs,inSize);        // uncompressed size
    while idxMs.Size mod 4 <> 0 do idxMs.WriteByte(0);
    crc:=CRC32Update(0,PByte(idxMs.Memory),idxMs.Size);
    idxMs.WriteByte(crc and $FF); idxMs.WriteByte((crc shr 8) and $FF);
    idxMs.WriteByte((crc shr 16) and $FF); idxMs.WriteByte((crc shr 24) and $FF);
    idxMs.Position:=0; OutStr.CopyFrom(idxMs,idxMs.Size);

    // === Stream footer ===
    idxSize:=idxMs.Size; backwardSize:=idxSize div 4-1;
    tmp[0]:=backwardSize and $FF; tmp[1]:=(backwardSize shr 8) and $FF;
    tmp[2]:=(backwardSize shr 16) and $FF; tmp[3]:=(backwardSize shr 24) and $FF;
    tmp[4]:=0; tmp[5]:=Byte(check);
    crc:=CRC32Update(0,@tmp[0],6);
    OutStr.WriteByte(crc and $FF); OutStr.WriteByte((crc shr 8) and $FF);
    OutStr.WriteByte((crc shr 16) and $FF); OutStr.WriteByte((crc shr 24) and $FF);
    OutStr.Write(tmp[0],4); OutStr.Write(tmp[4],2);
    OutStr.WriteByte($59); OutStr.WriteByte($5A);
  finally
    lzma2Ms.Free; idxMs.Free;
    if bcjBuf<>inBuf then FreeMem(bcjBuf);
  end;
end;

// ===========================================================================
// .xz Decoder (supports BCJ and Delta filter chains)
// ===========================================================================

procedure LZMA2DecompressStream(const InStr, OutStr: TStream);
var
  hdr: array[0..11] of Byte; crc, hdrCRC: LongWord;
  bSizeByte: Byte; bHdrSize: LongWord; bHdrBuf: PByte; off: Integer;
  flags: Byte; nFilters: Integer;
  filterID: array[0..3] of Int64; filterPropsSize: array[0..3] of Int64;
  filterProp: array[0..3] of Byte;
  fi: Integer; dictSizeProp: Byte; dictSize: LongWord;
  bcj: TBCJFilter; deltaDist: Integer; checkType: TXZCheckType;
  decompMs: TMemoryStream;
begin
  // Stream header
  if InStr.Read(hdr[0],12)<>12 then raise ELZMAError.Create('.xz: truncated stream header');
  if (hdr[0]<>$FD) or (hdr[1]<>$37) or (hdr[2]<>$7A) or
     (hdr[3]<>$58) or (hdr[4]<>$5A) or (hdr[5]<>$00) then
    raise ELZMAError.Create('.xz: bad magic');
  crc:=CRC32Update(0,@hdr[6],2);
  hdrCRC:=LongWord(hdr[8]) or (LongWord(hdr[9]) shl 8) or
          (LongWord(hdr[10]) shl 16) or (LongWord(hdr[11]) shl 24);
  if crc<>hdrCRC then raise ELZMAError.Create('.xz: stream header CRC mismatch');
  checkType:=TXZCheckType(hdr[7] and $0F);

  // Block header
  bSizeByte:=InStr.ReadByte;
  if bSizeByte=0 then raise ELZMAError.Create('.xz: no blocks');
  bHdrSize:=(LongWord(bSizeByte)+1)*4;  // spec: stored as (size/4)-1
  GetMem(bHdrBuf, bHdrSize);
  try
    bHdrBuf[0]:=bSizeByte;
    if InStr.Read(bHdrBuf[1], bHdrSize-1)<>Integer(bHdrSize-1) then
      raise ELZMAError.Create('.xz: truncated block header');
    crc:=CRC32Update(0,bHdrBuf,bHdrSize-4);
    hdrCRC:=LongWord(bHdrBuf[bHdrSize-4]) or (LongWord(bHdrBuf[bHdrSize-3]) shl 8) or
            (LongWord(bHdrBuf[bHdrSize-2]) shl 16) or (LongWord(bHdrBuf[bHdrSize-1]) shl 24);
    if crc<>hdrCRC then raise ELZMAError.Create('.xz: block header CRC mismatch');
    flags:=bHdrBuf[1];
    nFilters:=(flags and 3)+1;
    off:=2;
    if (flags and $40)<>0 then VLIFromBuf(bHdrBuf,off,bHdrSize);
    if (flags and $80)<>0 then VLIFromBuf(bHdrBuf,off,bHdrSize);
    for fi:=0 to nFilters-1 do begin
      filterID[fi]:=VLIFromBuf(bHdrBuf,off,bHdrSize);
      filterPropsSize[fi]:=VLIFromBuf(bHdrBuf,off,bHdrSize);
      if filterPropsSize[fi]>0 then begin filterProp[fi]:=bHdrBuf[off]; Inc(off, filterPropsSize[fi]); end
      else filterProp[fi]:=0;
    end;
    // Last filter must be LZMA2
    if filterID[nFilters-1]<>$21 then raise ELZMAError.Create('.xz: last filter must be LZMA2');
    dictSizeProp:=filterProp[nFilters-1];
    // Detect BCJ and Delta
    bcj:=bcjNone; deltaDist:=0;
    for fi:=0 to nFilters-2 do begin
      if filterID[fi]=$03 then deltaDist:=Integer(filterProp[fi])+1
      else bcj:=BCJFromID(Byte(filterID[fi]));
    end;
  finally FreeMem(bHdrBuf); end;

  if dictSizeProp>40 then raise ELZMAError.Create('.xz: bad dict size prop');
  if dictSizeProp=40 then dictSize:=$FFFFFFFF
  else dictSize:=(2 or LongWord(dictSizeProp and 1)) shl (LongWord(dictSizeProp) div 2+11);

  // Decompress LZMA2 into memory, then apply inverse filters
  if (bcj<>bcjNone) or (deltaDist>0) then begin
    decompMs:=TMemoryStream.Create;
    try
      LZMA2Decode(InStr, decompMs, dictSize);
      // Apply inverse filters in reverse order: Delta then BCJ
      if deltaDist>0 then DeltaDecode(PByte(decompMs.Memory), decompMs.Size, deltaDist);
      if bcj<>bcjNone then BCJApply(bcj, PByte(decompMs.Memory), decompMs.Size, False);
      decompMs.Position:=0; OutStr.CopyFrom(decompMs, decompMs.Size);
    finally decompMs.Free; end;
  end else
    LZMA2Decode(InStr, OutStr, dictSize);
  // (index/footer not validated — sufficient for decompression)
end;

// ===========================================================================
// .xz Stream compress (simple, default params)
// ===========================================================================

procedure LZMA2CompressStream(const InStr, OutStr: TStream);
var ms: TMemoryStream;
begin
  ms:=TMemoryStream.Create;
  try
    ms.CopyFrom(InStr,0);
    XZCompressEx(ms.Memory, ms.Size, OutStr,
                 LZMA_PRESETS[6].DictSizeProp,
                 LZMA_PRESETS[6].MFKind,
                 LZMA_PRESETS[6].NiceLen,
                 LZMA_PRESETS[6].MaxDepth,
                 xzCRC32, bcjNone, 0);
  finally ms.Free; end;
end;

// ===========================================================================
// Public API
// ===========================================================================

procedure LZMACompress(const InStr, OutStr: TStream);
begin
  LZMACompressStream(InStr, OutStr);
end;

procedure LZMADeCompress(const InStr, OutStr: TStream);
begin
  LZMADecompressStream(InStr, OutStr);
end;

procedure LZMA2Compress(const InStr, OutStr: TStream);
begin
  LZMA2CompressStream(InStr, OutStr);
end;

procedure LZMA2DeCompress(const InStr, OutStr: TStream);
begin
  LZMA2DecompressStream(InStr, OutStr);
end;

procedure LZMA2CompressEx(const InStr, OutStr: TStream; Level: Integer = 6;
                           Check: TXZCheckType = xzCRC32;
                           BCJ: TBCJFilter = bcjNone;
                           DeltaDist: Integer = 0);
var ms: TMemoryStream; preset: TLZMAPreset;
begin
  if Level<0 then Level:=0;
  if Level>9 then Level:=9;
  preset:=LZMA_PRESETS[Level];
  ms:=TMemoryStream.Create;
  try
    ms.CopyFrom(InStr,0);
    XZCompressEx(ms.Memory, ms.Size, OutStr,
                 preset.DictSizeProp, preset.MFKind, preset.NiceLen, preset.MaxDepth,
                 Check, BCJ, DeltaDist);
  finally ms.Free; end;
end;

function LZMA(const Uncompressed: AnsiString): AnsiString;
var InStr, OutStr: TStringStream;
begin
  InStr := TStringStream.Create(Uncompressed);
  OutStr := TStringStream.Create('');

  try
    LZMACompressStream(InStr, OutStr);
  finally
    InStr.Free;
  end;

  Result := OutStr.DataString;
  OutStr.Free;
end;

function UnLZMA(const Compressed: AnsiString): AnsiString;
var InStr, OutStr: TStringStream;
begin
  InStr := TStringStream.Create(Compressed);
  OutStr := TStringStream.Create('');

  try
    LZMADeCompressStream(InStr, OutStr);
  finally
    InStr.Free;
  end;

  Result := OutStr.DataString;
  OutStr.Free;
end;

function XZ(const Uncompressed: AnsiString): AnsiString;
var InStr, OutStr: TStringStream;
begin
  InStr := TStringStream.Create(Uncompressed);
  OutStr := TStringStream.Create('');

  try
    LZMA2CompressStream(InStr, OutStr);
  finally
    InStr.Free;
  end;

  Result := OutStr.DataString;
  OutStr.Free;
end;

function UnXZ(const Compressed: AnsiString): AnsiString;
var InStr, OutStr: TStringStream;
begin
  InStr := TStringStream.Create(Compressed);
  OutStr := TStringStream.Create('');

  try
    LZMA2DeCompressStream(InStr, OutStr);
  finally
    InStr.Free;
  end;

  Result := OutStr.DataString;
  OutStr.Free;
end;


//==============
procedure LZMACompressFile(const InFile, OutFile: String);
var InStr, OutStr: TFileSTream;
begin
  InStr := TFileSTream.Create(InFile, fmOpenRead or fmShareDenyWrite);
  OutStr := TFileStream.Create(OutFile, fmCreate);

  try
    LZMACompress(InStr, OutStr);
  finally
    InStr.Free;
    OutStr.Free;
  end;
end;

procedure LZMADeCompressFile(const InFile, OutFile: String);
var InStr, OutStr: TFileSTream;
begin
  InStr := TFileSTream.Create(InFile, fmOpenRead or fmShareDenyWrite);
  OutStr := TFileStream.Create(OutFile, fmCreate);

  try
    LZMADeCompress(InStr, OutStr);
  finally
    InStr.Free;
    OutStr.Free;
  end;
end;

procedure LZMA2CompressFile(const InFile, OutFile: String);
var InStr, OutStr: TFileSTream;
begin
  InStr := TFileSTream.Create(InFile, fmOpenRead or fmShareDenyWrite);
  OutStr := TFileStream.Create(OutFile, fmCreate);

  try
    LZMA2Compress(InStr, OutStr);
  finally
    InStr.Free;
    OutStr.Free;
  end;
end;

procedure LZMA2DeCompressFile(const InFile, OutFile: String);
var InStr, OutStr: TFileSTream;
begin
  InStr := TFileSTream.Create(InFile, fmOpenRead or fmShareDenyWrite);
  OutStr := TFileStream.Create(OutFile, fmCreate);

  try
    LZMA2DeCompress(InStr, OutStr);
  finally
    InStr.Free;
    OutStr.Free;
  end;
end;

initialization
  BuildCRCTable;

end.
