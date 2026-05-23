unit SHA256;
{$IFDEF FPC}{$MODE Delphi}{$H+}{$ENDIF}
{$R-}{$Q-}

//SHA-256 hashing
//Author: www.xelitan.com
//License: MIT

interface

type
  TSHA256Digest = array[0..31] of Byte;

// Hash len bytes starting at data; write 32-byte result into digest.
procedure SHA256_Buf(data: Pointer; len: NativeUInt; out digest: TSHA256Digest);

// Convenience: hash an AnsiString.
procedure SHA256_Str(const s: AnsiString; out digest: TSHA256Digest);

// THasherSHA256 wrapper (used by PBKDF2.pas)
type
  THasherSHA256 = class
  private
    FData: AnsiString;
  public
    constructor Create;
    // Append MsgLen bytes from Msg to the internal buffer.
    procedure Update(Msg: PByte; MsgLen: Integer);
    // Return final hash as uppercase hex (32 bytes → 64 chars).
    function Final: String;
    // Write raw 32-byte digest to an untyped var.
    procedure FinalRaw(var Digest);
  end;

implementation

uses SysUtils;

// SHA-256 round constants K[0..63]

const
  K: array[0..63] of LongWord = (
    $428a2f98, $71374491, $b5c0fbcf, $e9b5dba5,
    $3956c25b, $59f111f1, $923f82a4, $ab1c5ed5,
    $d807aa98, $12835b01, $243185be, $550c7dc3,
    $72be5d74, $80deb1fe, $9bdc06a7, $c19bf174,
    $e49b69c1, $efbe4786, $0fc19dc6, $240ca1cc,
    $2de92c6f, $4a7484aa, $5cb0a9dc, $76f988da,
    $983e5152, $a831c66d, $b00327c8, $bf597fc7,
    $c6e00bf3, $d5a79147, $06ca6351, $14292967,
    $27b70a85, $2e1b2138, $4d2c6dfc, $53380d13,
    $650a7354, $766a0abb, $81c2c92e, $92722c85,
    $a2bfe8a1, $a81a664b, $c24b8b70, $c76c51a3,
    $d192e819, $d6990624, $f40e3585, $106aa070,
    $19a4c116, $1e376c08, $2748774c, $34b0bcb5,
    $391c0cb3, $4ed8aa4a, $5b9cca4f, $682e6ff3,
    $748f82ee, $78a5636f, $84c87814, $8cc70208,
    $90befffa, $a4506ceb, $bef9a3f7, $c67178f2
  );

// ---------------------------------------------------------------------------
// Helpers — 32-bit operations only; explicit shl/shr to avoid intrinsic issues
// ---------------------------------------------------------------------------

function Ror32(x: LongWord; n: Byte): LongWord; inline;
begin
  Result := (x shr n) or (x shl (32 - n));
end;

// Read 4 bytes at p as a big-endian 32-bit word.
function Load32BE(p: PByte): LongWord; inline;
begin
  Result := (LongWord(p[0]) shl 24) or (LongWord(p[1]) shl 16)
         or (LongWord(p[2]) shl  8) or  LongWord(p[3]);
end;

// Write a 32-bit word to p in big-endian order.
procedure Store32BE(x: LongWord; p: PByte); inline;
begin
  p[0] := Byte(x shr 24);
  p[1] := Byte(x shr 16);
  p[2] := Byte(x shr  8);
  p[3] := Byte(x);
end;

// SHA-256 block compression (processes exactly 64 bytes at blk)
procedure SHA256_Block(var H: array of LongWord; blk: PByte);
var
  W: array[0..63] of LongWord;
  a, b, c, d, e, f, g, h_: LongWord;
  s0, s1, T1, T2, ch, maj: LongWord;
  i: Integer;
begin
  // Prepare message schedule
  for i := 0 to 15 do
    W[i] := Load32BE(blk + i * 4);
  for i := 16 to 63 do
  begin
    s0 := Ror32(W[i-15],  7) xor Ror32(W[i-15], 18) xor (W[i-15] shr  3);
    s1 := Ror32(W[i-2],  17) xor Ror32(W[i-2],  19) xor (W[i-2]  shr 10);
    W[i] := W[i-16] + s0 + W[i-7] + s1;
  end;

  // Initialise working variables
  a  := H[0]; b := H[1]; c := H[2]; d := H[3];
  e  := H[4]; f := H[5]; g := H[6]; h_ := H[7];

  // 64 rounds
  for i := 0 to 63 do
  begin
    s1  := Ror32(e,  6) xor Ror32(e, 11) xor Ror32(e, 25);
    ch  := (e and f) xor ((not e) and g);
    T1  := h_ + s1 + ch + K[i] + W[i];
    s0  := Ror32(a,  2) xor Ror32(a, 13) xor Ror32(a, 22);
    maj := (a and b) xor (a and c) xor (b and c);
    T2  := s0 + maj;
    h_  := g;
    g   := f;
    f   := e;
    e   := d + T1;
    d   := c;
    c   := b;
    b   := a;
    a   := T1 + T2;
  end;

  // Add compressed chunk to current hash value
  H[0] := H[0] + a;
  H[1] := H[1] + b;
  H[2] := H[2] + c;
  H[3] := H[3] + d;
  H[4] := H[4] + e;
  H[5] := H[5] + f;
  H[6] := H[6] + g;
  H[7] := H[7] + h_;
end;

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------
procedure SHA256_Buf(data: Pointer; len: NativeUInt; out digest: TSHA256Digest);
var
  H: array[0..7] of LongWord;
  block: array[0..63] of Byte;
  p: PByte;
  rem: NativeUInt;
  bitlen: UInt64;
begin
  // Initial hash values (FIPS 180-4 §5.3.3)
  H[0] := $6a09e667;  H[1] := $bb67ae85;
  H[2] := $3c6ef372;  H[3] := $a54ff53a;
  H[4] := $510e527f;  H[5] := $9b05688c;
  H[6] := $1f83d9ab;  H[7] := $5be0cd19;

  p   := PByte(data);
  rem := len;

  // Process complete 64-byte blocks
  while rem >= 64 do
  begin
    SHA256_Block(H, p);
    Inc(p, 64);
    Dec(rem, 64);
  end;

  // Final partial block — copy remaining bytes, add padding
  FillChar(block, SizeOf(block), 0);
  if rem > 0 then
    Move(p^, block[0], rem);
  block[rem] := $80;          // append bit '1'

  if rem >= 56 then
  begin
    // Not enough room for the 8-byte length field — need an extra block
    SHA256_Block(H, @block[0]);
    FillChar(block, SizeOf(block), 0);
  end;

  // Write 64-bit big-endian bit count into bytes 56-63
  bitlen := UInt64(len) shl 3;
  block[56] := Byte(bitlen shr 56);
  block[57] := Byte(bitlen shr 48);
  block[58] := Byte(bitlen shr 40);
  block[59] := Byte(bitlen shr 32);
  block[60] := Byte(bitlen shr 24);
  block[61] := Byte(bitlen shr 16);
  block[62] := Byte(bitlen shr  8);
  block[63] := Byte(bitlen);
  SHA256_Block(H, @block[0]);

  // Produce final digest (big-endian)
  Store32BE(H[0], @digest[ 0]);
  Store32BE(H[1], @digest[ 4]);
  Store32BE(H[2], @digest[ 8]);
  Store32BE(H[3], @digest[12]);
  Store32BE(H[4], @digest[16]);
  Store32BE(H[5], @digest[20]);
  Store32BE(H[6], @digest[24]);
  Store32BE(H[7], @digest[28]);
end;

procedure SHA256_Str(const s: AnsiString; out digest: TSHA256Digest);
begin
  if Length(s) > 0 then
    SHA256_Buf(@s[1], Length(s), digest)
  else
    SHA256_Buf(nil, 0, digest);
end;

// ---------------------------------------------------------------------------
// THasherSHA256 (streaming wrapper — buffers all data, hashes on FinalRaw)
// ---------------------------------------------------------------------------

constructor THasherSHA256.Create;
begin
  inherited;
  FData := '';
end;

procedure THasherSHA256.Update(Msg: PByte; MsgLen: Integer);
var
  old: Integer;
begin
  if MsgLen <= 0 then Exit;
  old := Length(FData);
  SetLength(FData, old + MsgLen);
  Move(Msg^, FData[old + 1], MsgLen);
end;

function THasherSHA256.Final: String;
var
  dig: TSHA256Digest;
  i: Integer;
begin
  SHA256_Str(FData, dig);
  Result := '';
  for i := 0 to 31 do
    Result := Result + IntToHex(dig[i], 2);
end;

procedure THasherSHA256.FinalRaw(var Digest);
var
  dig: TSHA256Digest;
begin
  SHA256_Str(FData, dig);
  Move(dig[0], Digest, 32);
end;

end.
