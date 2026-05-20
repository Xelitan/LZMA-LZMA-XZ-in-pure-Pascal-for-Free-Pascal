# Usage

```
procedure LZMACompress(const InStr, OutStr: TStream);
procedure LZMADeCompress(const InStr, OutStr: TStream);

procedure LZMACompressFile(const InFile, OutFile: String);
procedure LZMADeCompressFile(const InFile, OutFile: String); //unpacks .lzma

procedure LZMA2CompressFile(const InFile, OutFile: String);
procedure LZMA2DeCompressFile(const InFile, OutFile: String); //unpacks .xz

procedure LZMA2Compress(const InStr, OutStr: TStream);
procedure LZMA2DeCompress(const InStr, OutStr: TStream);
```
