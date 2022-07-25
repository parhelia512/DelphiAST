{-----------------------------------------------------------------------------
The contents of this file are subject to the Mozilla Public License Version
1.1 (the "License"); you may not use this file except in compliance with the
License. You may obtain a copy of the License at
http://www.mozilla.org/NPL/NPL-1_1Final.html

Software distributed under the License is distributed on an "AS IS" basis,
WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License for
the specific language governing rights and limitations under the License.

The Original Code is: mwPasLex.PAS, released August 17, 1999.

The Initial Developer of the Original Code is Martin Waldenburg
(Martin.Waldenburg@T-Online.de).
Portions created by Martin Waldenburg are Copyright (C) 1998, 1999 Martin
Waldenburg.
All Rights Reserved.

Contributor(s):  James Jacobson, LaKraven Studios Ltd, Roman Yankovsky
(This list is ALPHABETICAL)

Last Modified: mm/dd/yyyy
Current Version: 2.25

Notes: This program is a very fast Pascal tokenizer. I'd like to invite the
Delphi community to develop it further and to create a fully featured Object
Pascal parser.

Modification history:

LaKraven Studios Ltd, January 2015:

- Cleaned up version-specifics up to XE8
- Fixed all warnings & hints

Daniel Rolf between 20010723 and 20020116

Made ready for Delphi 6

platform
deprecated
varargs
local

Known Issues:
-----------------------------------------------------------------------------}

unit SimpleParser.Lexer;

{$IFDEF FPC}{$MODE DELPHI}{$ENDIF}

{$I SimpleParser.inc}

interface

uses
  SysUtils, Classes, Character,
  {$IFDEF FPC}
    Generics.Collections,
  {$ENDIF}
  SimpleParser.Lexer.Types;

{$IFDEF FPC}
const
  CompilerVersion = 0;
  RTLVersion = 0;
{$ENDIF}

var
  Identifiers: array[#0..#127] of ByteBool;
  mHashTable: array[#0..#127] of Integer;

type
  TmwBasePasLex = class;
  TDirectiveEvent = procedure(Sender: TmwBasePasLex) of object;
  TCommentEvent = procedure(Sender: TObject; const Text: string) of object;

  PDefineRec = ^TDefineRec;
  TDefineRec = record
    Defined: Boolean;
    StartCount: Integer;
    Next: PDefineRec;
  end;

  PBufferRec = ^TBufferRec;
  TBufferRec = record
    Buf: PChar;
    Run: Integer;
    SharedBuffer: Boolean;
    LineNumber: Integer;
    LinePos: Integer;
    FileName: string;
    Next: PBufferRec;
  end;

  TTokenLookup = record
    Name: string;
    Token, ExId: TptTokenKind;
  end;
  TTokenLooupTable = array[2..14,'A'..'X'] of TArray<TTokenLookup>;

  TmwBasePasLex = class(TObject)
  private
    FCommentState: TCommentState;
    FProcTable: array[#0..#127] of procedure of object;
    FBuffer: PBufferRec;
    RunAhead: Integer;
    TempRun: Integer;
    BufferSize: integer;
    FIdents: TTokenLooupTable;
    FTokenPos: Integer;
    FTokenID: TptTokenKind;
    FExID: TptTokenKind;
    FOnMessage: TMessageEvent;
    FOnCompDirect: TDirectiveEvent;
    FOnElseDirect: TDirectiveEvent;
    FOnEndIfDirect: TDirectiveEvent;
    FOnIfDefDirect: TDirectiveEvent;
    FOnIfNDefDirect: TDirectiveEvent;
    FOnResourceDirect: TDirectiveEvent;
    FOnIncludeDirect: TDirectiveEvent;
    FOnDefineDirect: TDirectiveEvent;
    FOnIfOptDirect: TDirectiveEvent;
    FOnIfDirect: TDirectiveEvent;
    FOnIfEndDirect: TDirectiveEvent;
    FOnElseIfDirect: TDirectiveEvent;
    FOnUnDefDirect: TDirectiveEvent;
    FDirectiveParamOrigin: PChar;
    FAsmCode: Boolean;
    FDefines: TArray<string>;
    FDefineStack: Integer;
    FTopDefineRec: PDefineRec;
    FUseDefines: Boolean;
    FScopedEnums: Boolean;
    FIncludeHandler: IIncludeHandler;
    FOnComment: TCommentEvent;

    function KeyHash: Integer;
    function KeyComp(const aKey: string): Boolean;
    procedure InitIdent;
    function GetPosXY: TTokenPoint; inline;
    procedure MakeMethodTables;
    procedure AddressOpProc;
    procedure AmpersandOpProc;
    procedure AsciiCharProc;
    procedure AnsiProc;
    procedure BinaryIntegerProc;
    procedure BorProc;
    procedure BraceCloseProc;
    procedure BraceOpenProc;
    procedure ColonProc;
    procedure CommaProc;
    procedure CRProc;
    procedure EqualProc;
    procedure GreaterProc;
    procedure IdentProc;
    procedure IntegerProc;
    procedure LFProc;
    procedure LowerProc;
    procedure MinusProc;
    procedure NullProc;
    procedure NumberProc;
    procedure PlusProc;
    procedure PointerSymbolProc;
    procedure PointProc;
    procedure RoundCloseProc;
    procedure RoundOpenProc;
    procedure SemiColonProc;
    procedure SlashProc;
    procedure SpaceProc;
    procedure SquareCloseProc;
    procedure SquareOpenProc;
    procedure StarProc;
    procedure StringProc;
    procedure StringDQProc;
    procedure SymbolProc;
    procedure UnknownProc;
    function GetToken: string; inline;
    function GetTokenLen: Integer; inline;
    function GetCompilerDirective: string;
    function GetDirectiveKind: TptTokenKind;
    function GetDirectiveParam: string;
    function GetStringContent: string;
    function GetIsJunk: Boolean; inline;
    function GetIsSpace: Boolean;
    function GetIsOrdIdent: Boolean;
    function GetIsRealType: Boolean;
    function GetIsStringType: Boolean;
    function GetIsVariantType: Boolean;
    function GetIsAddOperator: Boolean;
    function GetIsMulOperator: Boolean;
    function GetIsRelativeOperator: Boolean;
    function GetIsCompilerDirective: Boolean;
    function GetIsOrdinalType: Boolean;
    function GetGenID: TptTokenKind;

    procedure EnterDefineBlock(ADefined: Boolean);
    procedure ExitDefineBlock;
    procedure CloneDefinesFrom(ALexer: TmwBasePasLex);
    class function IsIdentifiersSlow(AChar: Char): Boolean; static;
    class function IsIdentifiers(AChar: Char): Boolean; static; inline;
    function HashValue(AChar: Char): Integer;
    function EvaluateComparison(AValue1: Extended; const AOper: String; AValue2: Extended): Boolean;
    function EvaluateConditionalExpression(const AParams: String): Boolean;
    procedure IncludeFile;
    function GetIncludeFileNameFromToken(const IncludeToken: string): string;
    function GetOrigin: string;
    function GetRunPos: Integer;
    procedure SetRunPos(const Value: Integer);
    procedure SetSharedBuffer(SharedBuffer: PBufferRec);
    procedure DisposeBuffer(Buf: PBufferRec);
    function GetFileName: string;
    procedure UpdateScopedEnums;
    procedure DoOnComment(index, count: Integer);
    function IdentLen: Integer;
    procedure Add(const name: string; token, exid: TptTokenKind);
  protected
    procedure SetOrigin(const NewValue: string); virtual;
  public
    constructor Create;
    destructor Destroy; override;
    function CharAhead: Char;
    procedure Next;
    procedure NextNoJunk;
    procedure NextNoSpace;
    procedure Init;
    procedure InitFrom(ALexer: TmwBasePasLex);
    function FirstInLine: Boolean;

    procedure AddDefine(const ADefine: string);
    procedure RemoveDefine(const ADefine: string);
    function IsDefined(const ADefine: string): Boolean;
    procedure ClearDefines;
    procedure InitDefinesDefinedByCompiler;

    property Buffer: PBufferRec read FBuffer;
    property CompilerDirective: string read GetCompilerDirective;
    property DirectiveParam: string read GetDirectiveParam;
    property IsJunk: Boolean read GetIsJunk;
    property IsSpace: Boolean read GetIsSpace;
    property Origin: string read GetOrigin write SetOrigin;
    property PosXY: TTokenPoint read GetPosXY;
    property RunPos: Integer read GetRunPos write SetRunPos;
    property Token: string read GetToken;
    property TokenLen: Integer read GetTokenLen;
    property TokenPos: Integer read FTokenPos;
    property TokenID: TptTokenKind read FTokenID;
    property ExID: TptTokenKind read FExID;
    property GenID: TptTokenKind read GetGenID;
    property StringContent: string read GetStringContent;
    property IsOrdIdent: Boolean read GetIsOrdIdent;
    property IsOrdinalType: Boolean read GetIsOrdinalType;
    property IsRealType: Boolean read GetIsRealType;
    property IsStringType: Boolean read GetIsStringType;
    property IsVariantType: Boolean read GetIsVariantType;
    property IsRelativeOperator: Boolean read GetIsRelativeOperator;
    property IsAddOperator: Boolean read GetIsAddOperator;
    property IsMulOperator: Boolean read GetIsMulOperator;
    property IsCompilerDirective: Boolean read GetIsCompilerDirective;
    property OnComment: TCommentEvent read FOnComment write FOnComment;
    property OnMessage: TMessageEvent read FOnMessage write FOnMessage;
    property OnCompDirect: TDirectiveEvent read FOnCompDirect write FOnCompDirect;
    property OnDefineDirect: TDirectiveEvent read FOnDefineDirect write FOnDefineDirect;
    property OnElseDirect: TDirectiveEvent read FOnElseDirect write FOnElseDirect;
    property OnEndIfDirect: TDirectiveEvent read FOnEndIfDirect write FOnEndIfDirect;
    property OnIfDefDirect: TDirectiveEvent read FOnIfDefDirect write FOnIfDefDirect;
    property OnIfNDefDirect: TDirectiveEvent read FOnIfNDefDirect write FOnIfNDefDirect;
    property OnIfOptDirect: TDirectiveEvent read FOnIfOptDirect write FOnIfOptDirect;
    property OnIncludeDirect: TDirectiveEvent read FOnIncludeDirect write FOnIncludeDirect;
    property OnIfDirect: TDirectiveEvent read FOnIfDirect write FOnIfDirect;
    property OnIfEndDirect: TDirectiveEvent read FOnIfEndDirect write FOnIfEndDirect;
    property OnElseIfDirect: TDirectiveEvent read FOnElseIfDirect write FOnElseIfDirect;
    property OnResourceDirect: TDirectiveEvent read FOnResourceDirect write FOnResourceDirect;
    property OnUnDefDirect: TDirectiveEvent read FOnUnDefDirect write FOnUnDefDirect;
    property AsmCode: Boolean read FAsmCode write FAsmCode;
    property DirectiveParamOrigin: PChar read FDirectiveParamOrigin;
    property UseDefines: Boolean read FUseDefines write FUseDefines;
    property ScopedEnums: Boolean read FScopedEnums;
    property IncludeHandler: IIncludeHandler read FIncludeHandler write FIncludeHandler;
    property FileName: string read GetFileName;
  end;

  TmwPasLex = class(TmwBasePasLex)
  private
    FAheadLex: TmwBasePasLex;
    function GetAheadExID: TptTokenKind;
    function GetAheadGenID: TptTokenKind;
    function GetAheadToken: string;
    function GetAheadTokenID: TptTokenKind;
  protected
    procedure SetOrigin(const NewValue: string); override;
  public
    constructor Create;
    destructor Destroy; override;
    procedure InitAhead;
    procedure AheadNext;
    property AheadLex: TmwBasePasLex read FAheadLex;
    property AheadToken: string read GetAheadToken;
    property AheadTokenID: TptTokenKind read GetAheadTokenID;
    property AheadExID: TptTokenKind read GetAheadExID;
    property AheadGenID: TptTokenKind read GetAheadGenID;
  end;

implementation

uses
  StrUtils;

type
  TmwPasLexExpressionEvaluation = (leeNone, leeAnd, leeOr);

procedure MakeIdentTable;
var
  I, J: Char;
begin
  for I := #0 to #127 do
  begin
    case I of
      '_', '0'..'9', 'a'..'z', 'A'..'Z': Identifiers[I] := True;
    else
      Identifiers[I] := False;
    end;
    J := UpperCase(I)[1];
    case I of
      'a'..'z', 'A'..'Z', '_': mHashTable[I] := Ord(J) - 64;
    else
      mHashTable[Char(I)] := 0;
    end;
  end;
end;

function TmwBasePasLex.CharAhead: Char;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  RunAhead := Buffer.Run;
  while (Buffer.Buf[RunAhead] > #0) and (Buffer.Buf[RunAhead] < #33) do
    Inc(RunAhead);
  Result := Buffer.Buf[RunAhead];
end;

procedure TmwBasePasLex.ClearDefines;
var
  Frame: PDefineRec;
begin
  while FTopDefineRec <> nil do
  begin
    Frame := FTopDefineRec;
    FTopDefineRec := Frame^.Next;
    Dispose(Frame);
  end;
  FDefines := nil;
  FDefineStack := 0;
end;

procedure TmwBasePasLex.CloneDefinesFrom(ALexer: TmwBasePasLex);
var
  Frame, LastFrame, SourceFrame: PDefineRec;
begin
  ClearDefines;
  FDefines := Copy(ALexer.FDefines);
  FDefineStack := ALexer.FDefineStack;

  Frame := nil;
  LastFrame := nil;
  SourceFrame := ALexer.FTopDefineRec;
  while SourceFrame <> nil do
  begin
    New(Frame);
    if FTopDefineRec = nil then
      FTopDefineRec := Frame
    else
      LastFrame^.Next := Frame;
    Frame^.Defined := SourceFrame^.Defined;
    Frame^.StartCount := SourceFrame^.StartCount;
    LastFrame := Frame;

    SourceFrame := SourceFrame^.Next;
  end;
  if Frame <> nil then
    Frame^.Next := nil;
end;

function TmwBasePasLex.GetPosXY: TTokenPoint;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  Result.X := FTokenPos - Buffer.LinePos + 1;
  Result.Y := Buffer.LineNumber + 1;
end;

function TmwBasePasLex.GetRunPos: Integer;
begin
  Result := FBuffer.Run;
end;

procedure TmwBasePasLex.Add(const name: string; token, exid: TptTokenKind);
var
  lookups: ^TArray<TTokenLookup>;
  len: Integer;
begin
  lookups := @FIdents[Length(name), Char(Word(name[1]) xor $20)];
  len := Length(lookups^);
  SetLength(lookups^, len + 1);
  lookups^[len].Name := UpperCase(name);
  lookups^[len].Token := token;
  lookups^[len].ExId := exid;
end;

procedure TmwBasePasLex.InitIdent;
begin
  Add('add', ptIdentifier, ptAdd);
  Add('if', ptIf, ptUnknown);
  Add('do', ptDo, ptUnknown);
  Add('and', ptAnd, ptUnknown);
  Add('as', ptAs, ptUnknown);
  Add('of', ptOf, ptUnknown);
  Add('at', ptIdentifier, ptAt);
  Add('end', ptEnd, ptUnknown);
  Add('in', ptIn, ptUnknown);
  Add('far', ptIdentifier, ptFar);
  Add('cdecl', ptIdentifier, ptCdecl);
  Add('read', ptIdentifier, ptRead);
  Add('case', ptCase, ptUnknown);
  Add('is', ptIs, ptUnknown);
  Add('on', ptIdentifier, ptOn);
//  Add('char', ptIdentifier, ptChar);
  Add('file', ptFile, ptUnknown);
  Add('label', ptLabel, ptUnknown);
  Add('mod', ptMod, ptUnknown);
  Add('or', ptOr, ptUnknown);
  Add('name', ptIdentifier, ptName);
  Add('asm', ptAsm, ptUnknown);
  Add('nil', ptNil, ptUnknown);
  Add('to', ptTo, ptUnknown);
  Add('div', ptDiv, ptUnknown);
//  Add('real', ptIdentifier, ptReal);
//  Add('real48', ptIdentifier, ptReal48);
  Add('begin', ptBegin, ptUnknown);
  Add('break', ptIdentifier, ptBreak);
  Add('near', ptIdentifier, ptNear);
  Add('for', ptFor, ptUnknown);
  Add('shl', ptShl, ptUnknown);
  Add('packed', ptPacked, ptUnknown);
  Add('var', ptVar, ptUnknown);
  Add('else', ptElse, ptUnknown);
  Add('halt', ptIdentifier, ptHalt);
  Add('final', ptIdentifier, ptFinal);
//  Add('int64', ptIdentifier, ptInt64);
  Add('local', ptIdentifier, ptLocal);
  Add('align', ptIdentifier, ptAlign);
  Add('set', ptSet, ptUnknown);
  Add('package', ptIdentifier, ptPackage);
  Add('shr', ptShr, ptUnknown);
//  Add('pchar', ptIdentifier, ptPChar);
  Add('sealed', ptSealed, ptUnknown);
  Add('then', ptThen, ptUnknown);
//  Add('comp', ptIdentifier, ptComp);
  Add('not', ptNot, ptUnknown);
//  Add('byte', ptIdentifier, ptByte);
  Add('raise', ptRaise, ptUnknown);
  Add('pascal', ptIdentifier, ptPascal);
  Add('class', ptClass, ptUnknown);
  Add('object', ptObject, ptUnknown);
  Add('index', ptIdentifier, ptIndex);
  Add('out', ptIdentifier, ptOut);
  Add('abort', ptIdentifier, ptAbort);
  Add('delayed', ptIdentifier, ptDelayed);
  Add('while', ptWhile, ptUnknown);
  Add('xor', ptXor, ptUnknown);
  Add('goto', ptGoto, ptUnknown);
  Add('exit', ptIdentifier, ptExit);
  Add('safecall', ptIdentifier, ptSafeCall);
//  Add('double', ptIdentifier, ptDouble);
  Add('with', ptWith, ptUnknown);
//  Add('word', ptIdentifier, ptWord);
  Add('dispid', ptIdentifier, ptDispid);
//  Add('cardinal', ptIdentifier, ptCardinal);
  Add('public', ptIdentifier, ptPublic);
  Add('array', ptArray, ptUnknown);
  Add('try', ptTry, ptUnknown);
  Add('record', ptRecord, ptUnknown);
  Add('inline', ptInline, ptInline);
//  Add('boolean', ptIdentifier, ptBoolean);
//  Add('dword', ptIdentifier, ptDWORD);
  Add('uses', ptUses, ptUnknown);
  Add('unit', ptUnit, ptUnknown);
  Add('helper', ptIdentifier, ptHelper);
  Add('repeat', ptRepeat, ptUnknown);
//  Add('single', ptIdentifier, ptSingle);
  Add('type', ptType, ptUnknown);
  Add('unsafe', ptIdentifier, ptUnsafe);
  Add('dynamic', ptIdentifier, ptDynamic);
  Add('default', ptIdentifier, ptDefault);
  Add('message', ptIdentifier, ptMessage);
//  Add('widechar', ptIdentifier, ptWideChar);
  Add('stdcall', ptIdentifier, ptStdcall);
  Add('const', ptConst, ptUnknown);
  Add('static', ptIdentifier, ptStatic);
  Add('except', ptExcept, ptUnknown);
  Add('write', ptIdentifier, ptWrite);
  Add('until', ptUntil, ptUnknown);
//  Add('integer', ptIdentifier, ptInteger);
  Add('remove', ptIdentifier, ptRemove); // ?
  Add('finally', ptFinally, ptUnknown);
  Add('reference', ptIdentifier, ptReference);
//  Add('extended', ptIdentifier, ptExtended);
  Add('stored', ptIdentifier, ptStored);
  Add('interface', ptInterface, ptUnknown);
  Add('deprecated', ptIdentifier, ptDeprecated);
  Add('abstract', ptIdentifier, ptAbstract);
  Add('library', ptLibrary, ptUnknown);
  Add('forward', ptIdentifier, ptForward);
//  Add('variant', ptIdentifier, ptVariant);
  Add('string', ptString, ptUnknown);
  Add('program', ptProgram, ptUnknown);
  Add('strict', ptIdentifier, ptStrict);
  Add('downto', ptDownto, ptUnknown);
  Add('private', ptIdentifier, ptPrivate);
//  Add('longint', ptIdentifier, ptLongint);
  Add('inherited', ptInherited, ptUnknown);
//  Add('longbool', ptIdentifier, ptLongBool);
  Add('overload', ptIdentifier, ptOverload);
  Add('resident', ptIdentifier, ptResident); // ?
  Add('readonly', ptIdentifier, ptReadonly);
  Add('assembler', ptIdentifier, ptAssembler);
  Add('contains', ptIdentifier, ptContains);
  Add('absolute', ptIdentifier, ptAbsolute);
//  Add('bytebool', ptIdentifier, ptByteBool);
  Add('override', ptIdentifier, ptOverride);
  Add('published', ptIdentifier, ptPublished);
  Add('threadvar', ptThreadvar, ptUnknown);
  Add('export', ptIdentifier, ptExport);
  Add('nodefault', ptIdentifier, ptNodefault);
  Add('external', ptIdentifier, ptExternal);
  Add('automated', ptIdentifier, ptAutomated); // ?
//  Add('smallint', ptIdentifier, ptSmallint);
  Add('register', ptIdentifier, ptRegister);
  Add('platform', ptIdentifier, ptPlatform);
  Add('continue', ptIdentifier, ptContinue);
  Add('function', ptFunction, ptUnknown);
  Add('virtual', ptIdentifier, ptVirtual);
//  Add('wordbool', ptIdentifier, ptWordBool);
  Add('procedure', ptProcedure, ptUnknown);
  Add('protected', ptIdentifier, ptProtected);
//  Add('currency', ptIdentifier, ptCurrency);
//  Add('longword', ptIdentifier, ptLongword);
  Add('operator', ptIdentifier, ptOperator);
  Add('requires', ptIdentifier, ptRequires);
  Add('exports', ptExports, ptUnknown);
//  Add('olevariant', ptIdentifier, ptOleVariant);
//  Add('shortint', ptIdentifier, ptShortint);
  Add('implements', ptIdentifier, ptImplements);
  Add('runerror', ptIdentifier, ptRunError);
//  Add('widestring', ptIdentifier, ptWideString);
  Add('dispinterface', ptDispinterface, ptUnknown);
//  Add('ansistring', ptIdentifier, ptAnsiString);
  Add('reintroduce', ptIdentifier, ptReintroduce);
  Add('property', ptProperty, ptUnknown);
  Add('finalization', ptFinalization, ptUnknown);
  Add('writeonly', ptIdentifier, ptWriteonly);
  Add('experimental', ptIdentifier, ptExperimental);
  Add('destructor', ptDestructor, ptUnknown);
  Add('constructor', ptConstructor, ptUnknown);
  Add('implementation', ptImplementation, ptUnknown);
//  Add('shortstring', ptIdentifier, ptShortString);
  Add('initialization', ptInitialization, ptUnknown);
  Add('resourcestring', ptResourcestring, ptUnknown);
  Add('stringresource', ptIdentifier, ptStringresource);
  Add('varargs', ptIdentifier, ptVarargs);
end;

function TmwBasePasLex.KeyHash: Integer;
var
  Buffer: PBufferRec;
  c: Char;
begin
  Result := 0;
  Buffer := FBuffer;
  while True do
  begin
    c := Buffer.Buf[Buffer.Run];
    if CharInSet(Char(Word(c) and not 32), ['A'..'Z']) or CharInSet(c, ['0'..'9', '_']) then
    begin
      Inc(Result, mHashTable[c]);
      Inc(Buffer.Run);
    end
    else if Ord(c) <= 127 then
      Break
    else if not IsIdentifiersSlow(c) then
      Break
    else
    begin
      Inc(Result, HashValue(c));
      Inc(Buffer.Run);
    end;
  end;
end;

function TmwBasePasLex.IdentLen: Integer;
var
  Buffer: PBufferRec;
  c: Char;
begin
  Result := 0;
  Buffer := FBuffer;
  while True do
  begin
    c := Buffer.Buf[Buffer.Run];
    if CharInSet(Char(Word(c) and not 32), ['A'..'Z']) or CharInSet(c, ['0'..'9', '_']) then
    begin
      Inc(Result);
      Inc(Buffer.Run);
    end
    else if Ord(c) <= 127 then
      Break
    else if not IsIdentifiersSlow(c) then
      Break
    else
    begin
      Inc(Result);
      Inc(Buffer.Run);
    end;
  end;
end;

function TmwBasePasLex.KeyComp(const aKey: string): Boolean;
label
  ReturnFalse;
var
  I, TokenLen: Integer;
  Temp: PChar;
begin
  // GetTokenLen not inlined because body below
  TokenLen := FBuffer.Run - FTokenPos;
  // aKey is not empty
  if PInteger(@PByte(aKey)[-4])^ = TokenLen then
  begin
    Temp := FBuffer.Buf + FTokenPos;
    for i := 1 to TokenLen do
      if mHashTable[Temp[i-1]] <> mHashTable[aKey[i]] then
        goto ReturnFalse;
    Result := True;
  end
  else
  ReturnFalse:
    Result := False;
end;

procedure TmwBasePasLex.MakeMethodTables;
var
  I: Char;
begin
  for I := #0 to #127 do
    case I of
      #0: FProcTable[I] := NullProc;
      #10: FProcTable[I] := LFProc;
      #13: FProcTable[I] := CRProc;
      #1..#9, #11, #12, #14..#32: FProcTable[I] := SpaceProc;
      '#': FProcTable[I] := AsciiCharProc;
      '$': FProcTable[I] := IntegerProc;
      '%': FProcTable[I] := BinaryIntegerProc;
      #39: FProcTable[I] := StringProc;
      '0'..'9': FProcTable[I] := NumberProc;
      'A'..'Z', 'a'..'z', '_': FProcTable[I] := IdentProc;
      '{': FProcTable[I] := BraceOpenProc;
      '}': FProcTable[I] := BraceCloseProc;
      '!', '"', '&', '('..'/', ':'..'@', '['..'^', '`', '~':
        begin
          case I of
            '(': FProcTable[I] := RoundOpenProc;
            ')': FProcTable[I] := RoundCloseProc;
            '*': FProcTable[I] := StarProc;
            '+': FProcTable[I] := PlusProc;
            ',': FProcTable[I] := CommaProc;
            '-': FProcTable[I] := MinusProc;
            '.': FProcTable[I] := PointProc;
            '/': FProcTable[I] := SlashProc;
            ':': FProcTable[I] := ColonProc;
            ';': FProcTable[I] := SemiColonProc;
            '<': FProcTable[I] := LowerProc;
            '=': FProcTable[I] := EqualProc;
            '>': FProcTable[I] := GreaterProc;
            '@': FProcTable[I] := AddressOpProc;
            '[': FProcTable[I] := SquareOpenProc;
            ']': FProcTable[I] := SquareCloseProc;
            '^': FProcTable[I] := PointerSymbolProc;
            '"': FProcTable[I] := StringDQProc;
            '&': FProcTable[I] := AmpersandOpProc;
          else
            FProcTable[I] := SymbolProc;
          end;
        end;
    else
      FProcTable[I] := UnknownProc;
    end;
end;

constructor TmwBasePasLex.Create;
begin
  inherited Create;
  InitIdent;
  MakeMethodTables;
  FExID := ptUnKnown;

  FUseDefines := True;
  FScopedEnums := False;
  FTopDefineRec := nil;
  ClearDefines;

  New(FBuffer);
  FillChar(FBuffer^, SizeOf(TBufferRec), 0);
end;

destructor TmwBasePasLex.Destroy;
begin
  if not FBuffer.SharedBuffer then
    FreeMem(FBuffer.Buf);

  Dispose(FBuffer);

  ClearDefines; //If we don't do this, we get a memory leak
  inherited Destroy;
end;

procedure TmwBasePasLex.DisposeBuffer(Buf: PBufferRec);
begin
  if Assigned(Buf.Buf) and not Buf.SharedBuffer then
    FreeMem(Buf.Buf);
  Dispose(Buf);
end;

procedure TmwBasePasLex.DoOnComment(index, count: Integer);
var
  CommentText: string;
begin
  if not FUseDefines or (FDefineStack = 0) then
  begin
    SetString(CommentText, PChar(@FBuffer.Buf[index]), count);
    FOnComment(Self, CommentText);
  end;
end;

procedure TmwBasePasLex.SetOrigin(const NewValue: string);
begin
  BufferSize := (Length(NewValue) + 1) * SizeOf(Char);

  ReallocMem(FBuffer.Buf, BufferSize);
  StrPCopy(FBuffer.Buf, NewValue);

  Init;
  Next;
end;

procedure TmwBasePasLex.SetRunPos(const Value: Integer);
begin
  FBuffer.Run := Value;
  Next;
end;

procedure TmwBasePasLex.SetSharedBuffer(SharedBuffer: PBufferRec);
var
  NextBuffer: PBufferRec;
begin
  while Assigned(FBuffer.Next) do
  begin
    NextBuffer := FBuffer;
    FBuffer := FBuffer.Next;
    DisposeBuffer(NextBuffer);
  end;

  if not FBuffer.SharedBuffer and Assigned(FBuffer.Buf) then
    FreeMem(FBuffer.Buf);

  FBuffer.Buf := SharedBuffer.Buf;
  FBuffer.Run := SharedBuffer.Run;
  FBuffer.LineNumber := SharedBuffer.LineNumber;
  FBuffer.LinePos := SharedBuffer.LinePos;
  FBuffer.SharedBuffer := True;

  Next;
end;

procedure TmwBasePasLex.AddDefine(const ADefine: string);
var
  len: Integer;
begin
  len := Length(FDefines);
  SetLength(FDefines, len + 1);
  FDefines[len] := ADefine;
end;

procedure TmwBasePasLex.AddressOpProc;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  case Buffer.Buf[Buffer.Run + 1] of
    '@':
      begin
        FTokenID := ptDoubleAddressOp;
        Inc(Buffer.Run, 2);
      end;
  else
    begin
      FTokenID := ptAddressOp;
      Inc(Buffer.Run);
    end;
  end;
end;

procedure TmwBasePasLex.AsciiCharProc;
var
  Buffer: PBufferRec;
begin
  FTokenID := ptAsciiChar;
  Buffer := FBuffer;
  Inc(Buffer.Run);
  if Buffer.Buf[Buffer.Run] = '$' then
  begin
    repeat
      Inc(Buffer.Run);
    until not CharInSet(Buffer.Buf[Buffer.Run], ['0'..'9', 'A'..'F', 'a'..'f']);
  end else
  begin
{$IFDEF SUPPORTS_INTRINSIC_HELPERS}
    while Char(Buffer.Buf[Buffer.Run]).IsDigit do
{$ELSE}
    while IsDigit(Buffer.Buf[Buffer.Run]) do
{$ENDIF}
      Inc(Buffer.Run);
  end;
end;

procedure TmwBasePasLex.BraceCloseProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptError;
  if Assigned(FOnMessage) then
    FOnMessage(Self, meError, 'Illegal character', PosXY.X, PosXY.Y);
end;

procedure TmwBasePasLex.BinaryIntegerProc;
var
  Buffer: PBufferRec;
begin
  FTokenID := ptIntegerConst;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
  until not CharInSet(Buffer.Buf[Buffer.Run], ['0', '1', '_']);
end;

procedure TmwBasePasLex.BorProc;
var
  Buffer: PBufferRec;
  BeginRun: Integer;
begin
  FTokenID := ptBorComment;
  Buffer := FBuffer;
  if Buffer.Buf[Buffer.Run] = #0 then
  begin
    NullProc;
    if Assigned(FOnMessage) then
      FOnMessage(Self, meError, 'Unexpected file end', PosXY.X, PosXY.Y);
    Exit;
  end;

  BeginRun := Buffer.Run;
  while Buffer.Buf[Buffer.Run] <> #0 do
    case Buffer.Buf[Buffer.Run] of
      '}':
        begin
          FCommentState := csNo;
          Inc(Buffer.Run);
          Break;
        end;
      #10:
        begin
          Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
      #13:
        begin
          Inc(Buffer.Run);
          if Buffer.Buf[Buffer.Run] = #10 then Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
    else
      Inc(Buffer.Run);
    end;

  if Assigned(FOnComment) then
    DoOnComment(BeginRun, Buffer.Run - BeginRun - 1);
end;

procedure TmwBasePasLex.BraceOpenProc;
var
  Buffer: PBufferRec;
  BeginRun: Integer;
begin
  Buffer := FBuffer;
  if Buffer.Buf[Buffer.Run + 1] = '$' then
    FTokenID := GetDirectiveKind
  else
  begin
    FTokenID := ptBorComment;
    FCommentState := csBor;
  end;

  Inc(Buffer.Run);
  BeginRun := Buffer.Run;
  while Buffer.Buf[Buffer.Run] <> #0 do
    case Buffer.Buf[Buffer.Run] of
      '}':
        begin
          FCommentState := csNo;
          Inc(Buffer.Run);
          Break;
        end;
      #10:
        begin
          Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
      #13:
        begin
          Inc(Buffer.Run);
          if Buffer.Buf[Buffer.Run] = #10 then Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
    else
      Inc(Buffer.Run);
    end;
  case FTokenID of
    ptBorComment:
      begin
        if Assigned(FOnComment) then
          DoOnComment(BeginRun, Buffer.Run - BeginRun - 1);
      end;
    ptCompDirect:
      begin
        if Assigned(FOnCompDirect) then
          FOnCompDirect(Self);
      end;
    ptDefineDirect:
      begin
        if FUseDefines and (FDefineStack = 0) then
          AddDefine(DirectiveParam);
        if Assigned(FOnDefineDirect) then
          FOnDefineDirect(Self);
      end;
    ptElseDirect:
      begin
        if FUseDefines then
        begin
          if FTopDefineRec <> nil then
          begin
            if FTopDefineRec^.Defined then
              Inc(FDefineStack)
            else
              if FDefineStack > 0 then
                Dec(FDefineStack);
          end;
        end;
        if Assigned(FOnElseDirect) then
          FOnElseDirect(Self);
      end;
    ptEndIfDirect:
      begin
        if FUseDefines then
          ExitDefineBlock;
        if Assigned(FOnEndIfDirect) then
          FOnEndIfDirect(Self);
      end;
    ptIfDefDirect:
      begin
        if FUseDefines then
          EnterDefineBlock(IsDefined(DirectiveParam));
        if Assigned(FOnIfDefDirect) then
          FOnIfDefDirect(Self);
      end;
    ptIfNDefDirect:
      begin
        if FUseDefines then
          EnterDefineBlock(not IsDefined(DirectiveParam));
        if Assigned(FOnIfNDefDirect) then
          FOnIfNDefDirect(Self);
      end;
    ptIfOptDirect:
      begin
        if FUseDefines then
          EnterDefineBlock(False);
        if Assigned(FOnIfOptDirect) then
          FOnIfOptDirect(Self);
      end;
    ptIfDirect:
      begin
        if FUseDefines then
          EnterDefineBlock(EvaluateConditionalExpression(DirectiveParam));
        if Assigned(FOnIfDirect) then
          FOnIfDirect(Self);
      end;
    ptIfEndDirect:
      begin
        if FUseDefines then
          ExitDefineBlock;
        if Assigned(FOnIfEndDirect) then
          FOnIfEndDirect(Self);
      end;
    ptElseIfDirect:
      begin
        if FUseDefines then
        begin
          if FTopDefineRec <> nil then
          begin
            if FTopDefineRec^.Defined then
              FDefineStack := FTopDefineRec.StartCount + 1
            else
            begin
              FDefineStack := FTopDefineRec.StartCount;
                if EvaluateConditionalExpression(DirectiveParam) then
                  FTopDefineRec^.Defined := True
                else
                  FDefineStack := FTopDefineRec.StartCount + 1
            end;
          end;
        end;
        if Assigned(FOnElseIfDirect) then
          FOnElseIfDirect(Self);
      end;
    ptIncludeDirect:
      begin
//        if Assigned(FOnIncludeDirect) then
//          FOnIncludeDirect(Self);
        if Assigned(FIncludeHandler) and (FDefineStack = 0) then
          IncludeFile
        else
          Next;
      end;
    ptResourceDirect:
      begin
        if Assigned(FOnResourceDirect) then
          FOnResourceDirect(Self);
      end;
    ptScopedEnumsDirect:
      begin
        UpdateScopedEnums;
      end;
    ptUndefDirect:
      begin
        if FUseDefines and (FDefineStack = 0) then
          RemoveDefine(DirectiveParam);
        if Assigned(FOnUnDefDirect) then
          FOnUnDefDirect(Self);
      end;
  end;
end;

function TmwBasePasLex.EvaluateComparison(AValue1: Extended; const AOper: String; AValue2: Extended): Boolean;
begin
  if AOper = '=' then
    Result := AValue1 = AValue2
  else if AOper = '<>' then
    Result := AValue1 <> AValue2
  else if AOper = '<' then
    Result := AValue1 < AValue2
  else if AOper = '<=' then
    Result := AValue1 <= AValue2
  else if AOper = '>' then
    Result := AValue1 > AValue2
  else if AOper = '>=' then
    Result := AValue1 >= AValue2
  else
    Result := False;
end;

function TmwBasePasLex.EvaluateConditionalExpression(const AParams: String): Boolean;
var
  LParams: String;
  LDefine: String;
  LEvaluation: TmwPasLexExpressionEvaluation;
  LIsComVer: Boolean;
  LIsRtlVer: Boolean;
  LOper: string;
  LValue: Integer;
  p, LBracketLevel: Integer;
begin
  { TODO : Expand support for <=> evaluations (complicated to do). Expand support for NESTED expressions }
  LEvaluation := leeNone;
  LParams := TrimLeft(AParams);
  LIsComVer := Pos('COMPILERVERSION', LParams) = 1;
  LIsRtlVer := Pos('RTLVERSION', LParams) = 1;
  if LIsComVer or LIsRtlVer then //simple parser which covers most frequent use cases
  begin
    Result := False;
    if LIsComVer then
      Delete(LParams, 1, Length('COMPILERVERSION'));
    if LIsRtlVer then
      Delete(LParams, 1, Length('RTLVERSION'));
    while (LParams <> '') and (LParams[1] = ' ') do
      Delete(LParams, 1, 1);
    p := Pos(' ', LParams);
    if p > 0 then
    begin
      LOper := Copy(LParams, 1, p-1);
      Delete(LParams, 1, p);
      while (LParams <> '') and (LParams[1] = ' ') do
        Delete(LParams, 1, 1);
      p := Pos(' ', LParams);
      if p = 0 then
        p := Length(LParams) + 1;
      if TryStrToInt(Copy(LParams, 1, p-1), LValue) then
      begin
        Delete(LParams, 1, p);
        while (LParams <> '') and (LParams[1] = ' ') do
          Delete(LParams, 1, 1);
        if LParams = '' then
          if LIsComVer then
            Result := EvaluateComparison(CompilerVersion, LOper, LValue)
          else if LIsRtlVer then
            Result := EvaluateComparison(RTLVersion, LOper, LValue);
      end;
    end;
  end else
  if (Pos('DEFINED(', LParams) = 1) or (Pos('NOT DEFINED(', LParams) = 1) or (LParams[1] = '(') then
  begin
    Result := True; // Optimistic
    repeat
      if Pos('DEFINED(', LParams) = 1 then
      begin
        LDefine := Copy(LParams, 9, Pos(')', LParams) - 9);
        LParams := TrimLeft(Copy(LParams, 10 + Length(LDefine), Length(AParams) - (9 + Length(LDefine))));
        case LEvaluation of
          leeNone: Result := IsDefined(LDefine);
          leeAnd: Result := Result and IsDefined(LDefine);
          leeOr: Result := Result or IsDefined(LDefine);
        end;
      end
      else if Pos('NOT DEFINED(', LParams) = 1 then
      begin
        LDefine := Copy(LParams, 13, Pos(')', LParams) - 13);
        LParams := TrimLeft(Copy(LParams, 14 + Length(LDefine), Length(AParams) - (13 + Length(LDefine))));
        case LEvaluation of
          leeNone: Result := (not IsDefined(LDefine));
          leeAnd: Result := Result and (not IsDefined(LDefine));
          leeOr: Result := Result or (not IsDefined(LDefine));
        end;
      end
      else if Pos('(', LParams) = 1 then
      begin
        LBracketLevel := 1;
        for p := 2 to Length(LParams) do
          case LParams[p] of
            '(': Inc(LBracketLevel);
            ')':
            begin
              Dec(LBracketLevel);
              if LBracketLevel = 0 then
                Break;
            end;
          end;
        if LBracketLevel = 0 then // matching closing bracket was found
        begin
          LDefine := Copy(LParams, 2, p - 2);
          LParams := TrimLeft(Copy(LParams, p + 1));
          case LEvaluation of
            leeNone: Result := EvaluateConditionalExpression(LDefine);
            leeAnd: Result := Result and EvaluateConditionalExpression(LDefine);
            leeOr: Result := Result or EvaluateConditionalExpression(LDefine);
          end;
        end;
      end;
      // Determine next Evaluation
      if Pos('AND ', LParams) = 1 then
      begin
        LEvaluation := leeAnd;
        LParams := TrimLeft(Copy(LParams, 4, Length(LParams) - 3));
      end
      else if Pos('OR ', LParams) = 1 then
      begin
        LEvaluation := leeOr;
        LParams := TrimLeft(Copy(LParams, 3, Length(LParams) - 2));
      end;
    until not ((Pos('DEFINED(', LParams) = 1) or (Pos('NOT DEFINED(', LParams) = 1) or (Pos('(', LParams) = 1));
  end else
    Result := False;
end;

procedure TmwBasePasLex.ColonProc;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  if Buffer.Buf[Buffer.Run + 1] = '=' then
  begin
    Inc(Buffer.Run, 2);
    FTokenID := ptAssign;
  end
  else
  begin
    Inc(Buffer.Run);
    FTokenID := ptColon;
  end;
end;

procedure TmwBasePasLex.CommaProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptComma;
end;

procedure TmwBasePasLex.CRProc;
var
  Buffer: PBufferRec;
begin
  case FCommentState of
    csBor: FTokenID := ptCRLFCo;
    csAnsi: FTokenID := ptCRLFCo;
  else
    FTokenID := ptCRLF;
  end;

  Buffer := FBuffer;
  case Buffer.Buf[Buffer.Run + 1] of
    #10: Inc(Buffer.Run, 2);
  else
    Inc(Buffer.Run);
  end;
  Inc(Buffer.LineNumber);
  Buffer.LinePos := Buffer.Run;
end;

procedure TmwBasePasLex.EnterDefineBlock(ADefined: Boolean);
var
  StackFrame: PDefineRec;
begin
  New(StackFrame);
  StackFrame^.Next := FTopDefineRec;
  StackFrame^.Defined := ADefined;
  StackFrame^.StartCount := FDefineStack;
  FTopDefineRec := StackFrame;
  if not ADefined then
    Inc(FDefineStack);
end;

procedure TmwBasePasLex.EqualProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptEqual;
end;

procedure TmwBasePasLex.ExitDefineBlock;
var
  StackFrame: PDefineRec;
begin
  StackFrame := FTopDefineRec;
  if StackFrame <> nil then
  begin
    FDefineStack := StackFrame^.StartCount;
    FTopDefineRec := StackFrame^.Next;
    Dispose(StackFrame);
  end;
end;

procedure TmwBasePasLex.GreaterProc;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  if Buffer.Buf[Buffer.Run + 1] = '=' then
  begin
    Inc(Buffer.Run, 2);
    FTokenID := ptGreaterEqual;
  end
  else
  begin
    Inc(Buffer.Run);
    FTokenID := ptGreater;
  end;
end;

function TmwBasePasLex.HashValue(AChar: Char): Integer;
begin
  if AChar <= #127 then
    Result := mHashTable[AChar]
  else
    Result := Ord(AChar);
end;

procedure TmwBasePasLex.IdentProc;
var
  Buffer: PBufferRec;
  c: Char;
  len, i, n: Integer;
  Temp: PChar;
  lookups: ^TArray<TTokenLookup>;
begin
  Buffer := FBuffer;
  c := Char(Word(Buffer.Buf[Buffer.Run]) and not 32);
  len := IdentLen;
  if (len in [2..14]) and CharInSet(c, ['A'..'X']) then
  begin
    Temp := Buffer.Buf + FTokenPos;
    lookups := @FIdents[len, c];
    for i := 0 to High(lookups^) do
    begin
      for n := 2 to len do
        if lookups^[i].Name[n] <> Char(Word(temp[n-1]) and not 32) then
          Break;
      if n > len then
      begin
        if lookups^[i].ExId <> ptUnknown then
          FExID := lookups^[i].ExId;
        FTokenID := lookups^[i].Token;
        Exit;
      end;
    end;
  end;
  FTokenID := ptIdentifier;
end;

procedure TmwBasePasLex.IntegerProc;
var
  Buffer: PBufferRec;
begin
  FTokenID := ptIntegerConst;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
  until not CharInSet(Buffer.Buf[Buffer.Run], ['0'..'9', 'A'..'F', 'a'..'f', '_']);
end;

function TmwBasePasLex.IsDefined(const ADefine: string): Boolean;
var
  i: Integer;
begin
  for i := 0 to High(FDefines) do
    if SameText(FDefines[i], ADefine) then
      Exit(True);
  Result := False;
end;

class function TmwBasePasLex.IsIdentifiersSlow(AChar: Char): Boolean;
begin
  {$IF RTLVersion >= 25}
  Result := AChar.IsLetterOrDigit
    or (not AChar.IsHighSurrogate and not AChar.IsLowSurrogate);
  {$ELSE}
  Result := TCharacter.IsLetterOrDigit(AChar)
    or (not TCharacter.IsHighSurrogate(AChar) and not TCharacter.IsLowSurrogate(AChar));
  {$IFEND}
end;

class function TmwBasePasLex.IsIdentifiers(AChar: Char): Boolean;
begin
  // assuming Delphi identifier may include letters, digits, underscore symbol
  // and any character over 127 except surrogates
  if CharInSet(AChar, ['a'..'z', 'A'..'Z', '0'..'9', '_']) then
    Result := True
  else if Ord(AChar) <= 127 then
    Result := False
  else
    Result := IsIdentifiersSlow(AChar);
end;

procedure TmwBasePasLex.LFProc;
var
  Buffer: PBufferRec;
begin
  case FCommentState of
    csBor: FTokenID := ptCRLFCo;
    csAnsi: FTokenID := ptCRLFCo;
  else
    FTokenID := ptCRLF;
  end;
  Buffer := FBuffer;
  Inc(Buffer.Run);
  Inc(Buffer.LineNumber);
  Buffer.LinePos := Buffer.Run;
end;

procedure TmwBasePasLex.LowerProc;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  case Buffer.Buf[Buffer.Run + 1] of
    '=':
      begin
        Inc(Buffer.Run, 2);
        FTokenID := ptLowerEqual;
      end;
    '>':
      begin
        Inc(Buffer.Run, 2);
        FTokenID := ptNotEqual;
      end
  else
    begin
      Inc(Buffer.Run);
      FTokenID := ptLower;
    end;
  end;
end;

procedure TmwBasePasLex.MinusProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptMinus;
end;

procedure TmwBasePasLex.NullProc;
var
  OldBuffer: PBufferRec;
begin
  if Assigned(FBuffer.Next) then
  begin
    OldBuffer := FBuffer;
    FBuffer := FBuffer.Next;
    DisposeBuffer(OldBuffer);

    Next;
  end else
    FTokenID := ptNull;
end;

procedure TmwBasePasLex.NumberProc;
var
  Buffer: PBufferRec;
  c: Char;
begin
  FTokenID := ptIntegerConst;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
    c := Buffer.Buf[Buffer.Run];
    if c = '.' then
      if Buffer.Buf[Buffer.Run + 1] = '.' then
        Break
      else
        FTokenID := ptFloat;
  until not CharInSet(c, ['0'..'9', '.', 'e', 'E', '_']);
end;

procedure TmwBasePasLex.PlusProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptPlus;
end;

procedure TmwBasePasLex.PointerSymbolProc;
const
  PointerChars = ['a'..'z', 'A'..'Z', '\', '!', '"', '#', '$', '%', '&', '''',
                  '?', '@', '_', '`', '|', '}', '~'];
                  // TODO: support ']', '), ''*', '+', ',', '-', '.', '/', ':', ';', '<', '=', '>', '{', '^', '(', '['
var
  Buffer: PBufferRec;
begin
  FTokenID := ptPointerSymbol;
  Buffer := FBuffer;
  Inc(Buffer.Run);

  //This is a wierd Pascal construct that rarely appears, but needs to be
  //supported. ^M is a valid char reference (#13, in this case)
  if CharInSet(Buffer.Buf[Buffer.Run], PointerChars) and not IsIdentifiers(Buffer.Buf[Buffer.Run + 1]) then
  begin
    Inc(Buffer.Run);
    FTokenID := ptAsciiChar;
  end;
end;

procedure TmwBasePasLex.PointProc;
var
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  case Buffer.Buf[Buffer.Run + 1] of
    '.':
      begin
        Inc(Buffer.Run, 2);
        FTokenID := ptDotDot;
      end;
    ')':
      begin
        Inc(Buffer.Run, 2);
        FTokenID := ptSquareClose;
      end;
  else
    begin
      Inc(Buffer.Run);
      FTokenID := ptPoint;
    end;
  end;
end;

procedure Delete(var values: TArray<string>; index: Integer);
var
  len: Integer;
  tailCount: Integer;
begin
  len := Length(values);
  if len = 0 then
    Exit;
  values[index] := '';
  tailCount := len - (index + 1);
  if tailCount > 0 then
    Move(values[index + 1], values[index], SizeOf(string) * tailCount);
  Pointer(values[len - 1]) := nil; // do not trigger string refcounting as we moved it
  SetLength(values, len - 1);
end;

procedure TmwBasePasLex.RemoveDefine(const ADefine: string);
var
  i: Integer;
begin
  for i := High(FDefines) downto 0 do
    if SameText(FDefines[i], ADefine) then
      Delete(FDefines, i);
end;

procedure TmwBasePasLex.RoundCloseProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptRoundClose;
end;

procedure TmwBasePasLex.AnsiProc;
var
  Buffer: PBufferRec;
  BeginRun: Integer;
begin
  FTokenID := ptAnsiComment;
  Buffer := FBuffer;
  if Buffer.Buf[Buffer.Run] = #0 then
  begin
    NullProc;
    if Assigned(FOnMessage) then
      FOnMessage(Self, meError, 'Unexpected file end', PosXY.X, PosXY.Y);
    Exit;
  end;

  BeginRun := Buffer.Run + 1;
  while Buffer.Buf[Buffer.Run] <> #0 do
    case Buffer.Buf[Buffer.Run] of
      '*':
        if Buffer.Buf[Buffer.Run + 1] = ')' then
        begin
          FCommentState := csNo;
          Inc(Buffer.Run, 2);
          Break;
        end
        else
          Inc(Buffer.Run);
      #10:
        begin
          Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
      #13:
        begin
          Inc(Buffer.Run);
          if Buffer.Buf[Buffer.Run] = #10 then Inc(Buffer.Run);
          Inc(Buffer.LineNumber);
          Buffer.LinePos := Buffer.Run;
        end;
    else
      Inc(Buffer.Run);
    end;

  if Assigned(FOnComment) then
    DoOnComment(BeginRun, Buffer.Run - BeginRun - 2);
end;

procedure TmwBasePasLex.RoundOpenProc;
var
  Buffer: PBufferRec;
  BeginRun: Integer;
begin
  Buffer := FBuffer;
  BeginRun := Buffer.Run + 2;
  Inc(Buffer.Run);
  case Buffer.Buf[Buffer.Run] of
    '*':
      begin
        FTokenID := ptAnsiComment;
        if Buffer.Buf[Buffer.Run + 1] = '$' then
          FTokenID := GetDirectiveKind
        else
          FCommentState := csAnsi;
        Inc(Buffer.Run);
        while Buffer.Buf[Buffer.Run] <> #0 do
          case Buffer.Buf[Buffer.Run] of
            '*':
              if Buffer.Buf[Buffer.Run + 1] = ')' then
              begin
                FCommentState := csNo;
                Inc(Buffer.Run, 2);
                Break;
              end
              else
                Inc(Buffer.Run);
            #10:
              begin
                Inc(Buffer.Run);
                Inc(Buffer.LineNumber);
                Buffer.LinePos := Buffer.Run;
              end;
            #13:
              begin
                Inc(Buffer.Run);
                if Buffer.Buf[Buffer.Run] = #10 then Inc(Buffer.Run);
                Inc(Buffer.LineNumber);
                Buffer.LinePos := Buffer.Run;
              end;
          else
            Inc(Buffer.Run);
          end;
      end;
    '.':
      begin
        Inc(Buffer.Run);
        FTokenID := ptSquareOpen;
      end;
  else
    FTokenID := ptRoundOpen;
  end;
  case FTokenID of
    PtAnsiComment:
      begin
        if Assigned(FOnComment) then
          DoOnComment(BeginRun, Buffer.Run - BeginRun - 2);
      end;
    PtCompDirect:
      begin
        if Assigned(FOnCompDirect) then
          FOnCompDirect(Self);
      end;
    PtDefineDirect:
      begin
        if Assigned(FOnDefineDirect) then
          FOnDefineDirect(Self);
      end;
    PtElseDirect:
      begin
        if Assigned(FOnElseDirect) then
          FOnElseDirect(Self);
      end;
    PtEndIfDirect:
      begin
        if Assigned(FOnEndIfDirect) then
          FOnEndIfDirect(Self);
      end;
    PtIfDefDirect:
      begin
        if Assigned(FOnIfDefDirect) then
          FOnIfDefDirect(Self);
      end;
    PtIfNDefDirect:
      begin
        if Assigned(FOnIfNDefDirect) then
          FOnIfNDefDirect(Self);
      end;
    PtIfOptDirect:
      begin
        if Assigned(FOnIfOptDirect) then
          FOnIfOptDirect(Self);
      end;
    PtIncludeDirect:
      begin
        if Assigned(FIncludeHandler) then
          IncludeFile;
      end;
    PtResourceDirect:
      begin
        if Assigned(FOnResourceDirect) then
          FOnResourceDirect(Self);
      end;
    PtScopedEnumsDirect:
      begin
        UpdateScopedEnums;
      end;
    PtUndefDirect:
      begin
        if Assigned(FOnUnDefDirect) then
          FOnUnDefDirect(Self);
      end;
  end;
end;

procedure TmwBasePasLex.SemiColonProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptSemiColon;
end;

procedure TmwBasePasLex.SlashProc;
var
  BeginRun: Integer;
  Buffer: PBufferRec;
begin
  Buffer := FBuffer;
  case Buffer.Buf[Buffer.Run + 1] of
    '/':
      begin
        Inc(Buffer.Run, 2);

        BeginRun := Buffer.Run;

        FTokenID := ptSlashesComment;
        while not CharInSet(Buffer.Buf[Buffer.Run], [#0, #10, #13]) do
          Inc(Buffer.Run);

        if Assigned(FOnComment) then
          DoOnComment(BeginRun, Buffer.Run - BeginRun);
      end;
  else
    begin
      Inc(Buffer.Run);
      FTokenID := ptSlash;
    end;
  end;
end;

procedure TmwBasePasLex.SpaceProc;
var
  Buffer: PBufferRec;
  c: Char;
begin
  FTokenID := ptSpace;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
    c := Buffer.Buf[Buffer.Run];
  until (Ord(c) > 32) or (c = #13) or (c = #10) or (c = #0);
end;

procedure TmwBasePasLex.SquareCloseProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptSquareClose;
end;

procedure TmwBasePasLex.SquareOpenProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptSquareOpen;
end;

procedure TmwBasePasLex.StarProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptStar;
end;

procedure TmwBasePasLex.StringProc;
var
  Buffer: PBufferRec;
begin
  FTokenID := ptStringConst;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
    case Buffer.Buf[Buffer.Run] of
      #0, #10, #13:
        begin
          if Assigned(FOnMessage) then
            FOnMessage(Self, meError, 'Unterminated string', PosXY.X, PosXY.Y);
          Break;
        end;
      #39:
        while (Buffer.Buf[Buffer.Run] = #39) and (Buffer.Buf[Buffer.Run + 1] = #39) do
          Inc(Buffer.Run, 2);
    end;
  until Buffer.Buf[Buffer.Run] = #39;
  if Buffer.Buf[Buffer.Run] = #39 then
  begin
    Inc(Buffer.Run);
    if TokenLen = 3 then
      FTokenID := ptAsciiChar;
  end;
end;

procedure TmwBasePasLex.SymbolProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptSymbol;
end;

procedure TmwBasePasLex.UnknownProc;
begin
  Inc(FBuffer.Run);
  FTokenID := ptUnknown;
  if Assigned(FOnMessage) then
   FOnMessage(Self, meError, 'Unknown Character', PosXY.X, PosXY.Y);
end;

procedure TmwBasePasLex.Next;
var
  Buffer: PBufferRec;
  Run: Integer;
  c: Char;
begin
  FExID := ptUnKnown;
  Buffer := FBuffer;
  Run := Buffer.Run;
  FTokenPos := Run;
  case FCommentState of
    csNo:
    begin
      c := Buffer.Buf[Run];
      if Ord(c) <= 127 then
        FProcTable[c]
      else
        IdentProc;
    end;
    csBor: BorProc;
    csAnsi: AnsiProc;
  end;
end;

function TmwBasePasLex.GetIsJunk: Boolean;
begin
  Result := IsTokenIDJunk(FTokenID) or (FUseDefines and (FDefineStack > 0) and (TokenID <> ptNull));
end;

function TmwBasePasLex.GetIsSpace: Boolean;
begin
  Result := FTokenID in [ptCRLF, ptSpace];
end;

function TmwBasePasLex.GetTokenLen: Integer;
begin
  Result := FBuffer.Run - FTokenPos;
end;

function TmwBasePasLex.GetToken: string;
begin
  SetString(Result, FBuffer.Buf + FTokenPos, TokenLen);
end;

procedure TmwBasePasLex.NextNoJunk;
begin
  repeat
    Next;
  until not IsJunk;
end;

procedure TmwBasePasLex.NextNoSpace;
begin
  repeat
    Next;
  until not IsSpace;
end;

function TmwBasePasLex.FirstInLine: Boolean;
var
  Buffer: PBufferRec;
  RunBack: Integer;
begin
  Result := True;
  if FTokenPos = 0 then Exit;
  RunBack := FTokenPos;
  Buffer := FBuffer;
  repeat
    Dec(RunBack);
  until not CharInSet(Buffer.Buf[RunBack], [#1..#9, #11, #12, #14..#32]);
  if RunBack = 0 then Exit;
  case Buffer.Buf[RunBack] of
    #10, #13: Exit;
  else
    begin
      Result := False;
      Exit;
    end;
  end;
end;

function TmwBasePasLex.GetCompilerDirective: string;
var
  Buffer: PBufferRec;
  DirectLen: Integer;
begin
  if TokenID <> ptCompDirect then
    Result := ''
  else
  begin
    Buffer := FBuffer;
    case Buffer.Buf[FTokenPos] of
      '(':
        begin
          DirectLen := Buffer.Run - FTokenPos - 4;
          SetString(Result, (Buffer.Buf + FTokenPos + 2), DirectLen);
          Result := UpperCase(Result);
        end;
      '{':
        begin
          DirectLen := Buffer.Run - FTokenPos - 2;
          SetString(Result, (Buffer.Buf + FTokenPos + 1), DirectLen);
          Result := UpperCase(Result);
        end;
    end;
  end;
end;

function TmwBasePasLex.GetDirectiveKind: TptTokenKind;
var
  Buffer: PBufferRec;
  TempPos: Integer;
begin
  Buffer := FBuffer;
  case Buffer.Buf[FTokenPos] of
    '(': Buffer.Run := FTokenPos + 3;
    '{': Buffer.Run := FTokenPos + 2;
  end;
  FDirectiveParamOrigin := Buffer.Buf + FTokenPos;
  TempPos := FTokenPos;
  FTokenPos := Buffer.Run;
  case KeyHash of
    9:
      if KeyComp('I') and (not CharInSet(Buffer.Buf[Buffer.Run], ['+', '-'])) then
        Result := ptIncludeDirect else
        Result := ptCompDirect;
    15:
      if KeyComp('IF') then
        Result := ptIfDirect else
        Result := ptCompDirect;
    18:
      if KeyComp('R') then
      begin
        if not CharInSet(Buffer.Buf[Buffer.Run], ['+', '-']) then
          Result := ptResourceDirect else Result := ptCompDirect;
      end else Result := ptCompDirect;
    30:
      if KeyComp('IFDEF') then
        Result := ptIfDefDirect else
        Result := ptCompDirect;
    38:
      if KeyComp('ENDIF') then
        Result := ptEndIfDirect else
      if KeyComp('IFEND') then
        Result := ptIfEndDirect else
        Result := ptCompDirect;
    41:
      if KeyComp('ELSE') then
        Result := ptElseDirect else
        Result := ptCompDirect;
    43:
      if KeyComp('DEFINE') then
        Result := ptDefineDirect else
        Result := ptCompDirect;
    44:
      if KeyComp('IFNDEF') then
        Result := ptIfNDefDirect else
        Result := ptCompDirect;
    50:
      if KeyComp('UNDEF') then
        Result := ptUndefDirect else
        Result := ptCompDirect;
    56:
      if KeyComp('ELSEIF') then
        Result := ptElseIfDirect else
        Result := ptCompDirect;
    66:
      if KeyComp('IFOPT') then
        Result := ptIfOptDirect else
        Result := ptCompDirect;
    68:
      if KeyComp('INCLUDE') then
        Result := ptIncludeDirect else
        Result := ptCompDirect;
    104:
      if KeyComp('Resource') then
        Result := ptResourceDirect else
        Result := ptCompDirect;
    134:
      if KeyComp('SCOPEDENUMS') then
        Result := ptScopedEnumsDirect else
        Result := ptCompDirect;
  else
    Result := ptCompDirect;
  end;
  FTokenPos := TempPos;
  Dec(Buffer.Run);
end;

function TmwBasePasLex.GetDirectiveParam: string;
var
  Buffer: PBufferRec;
  EndPos: Integer;
  ParamLen: Integer;
begin
  Buffer := FBuffer;
  case Buffer.Buf[FTokenPos] of
    '(':
      begin
        TempRun := FTokenPos + 3;
        EndPos := Buffer.Run - 2;
      end;
    '{':
      begin
        TempRun := FTokenPos + 2;
        EndPos := Buffer.Run - 1;
      end;
  else
    EndPos := 0;
  end;
  while IsIdentifiers(Buffer.Buf[TempRun]) do
    Inc(TempRun);
  while CharInSet(Buffer.Buf[TempRun], ['+', ',', '-']) do
  begin
    repeat
      Inc(TempRun);
    until not IsIdentifiers(Buffer.Buf[TempRun]);
    if CharInSet(Buffer.Buf[TempRun - 1], ['+', ',', '-']) and (Buffer.Buf[TempRun] = ' ') then Inc(TempRun);
  end;

  while CharInSet(Buffer.Buf[TempRun], [' ', #9]) do Inc(TempRun);
  while CharInSet(Buffer.Buf[EndPos - 1], [' ', #9]) do Dec(EndPos);

  ParamLen := EndPos - TempRun;
  SetString(Result, (Buffer.Buf + TempRun), ParamLen);
  Result := UpperCase(Result);
end;

function TmwBasePasLex.GetFileName: string;
begin
  Result := Buffer.FileName;
end;

function TmwBasePasLex.GetIncludeFileNameFromToken(const IncludeToken: string): string;
var
  FileNameStartPos, CurrentPos: integer;
  TrimmedToken: string;
  QuotedFileName: Boolean;
begin
  TrimmedToken := Trim(IncludeToken);
  CurrentPos := 1;
  while TrimmedToken[CurrentPos] > #32 do
    inc(CurrentPos);
  while TrimmedToken[CurrentPos] <= #32 do
    inc(CurrentPos);
  QuotedFileName := TrimmedToken[CurrentPos] = '''';
  if QuotedFileName then
    inc(CurrentPos);
  FileNameStartPos := CurrentPos;
  while (TrimmedToken[CurrentPos] <> '}')
    and (TrimmedToken[CurrentPos] <> '''')
    and ((TrimmedToken[CurrentPos] > #32) or QuotedFileName)
  do
    inc(CurrentPos);

  Result := Copy(TrimmedToken, FileNameStartPos, CurrentPos - FileNameStartPos);
end;

procedure TmwBasePasLex.IncludeFile;
var
  IncludeName, IncludeDirective, Content, FileName: string;
  NewBuffer: PBufferRec;
begin
  IncludeDirective := Token;
  IncludeName := GetIncludeFileNameFromToken(IncludeDirective);

  if FIncludeHandler.GetIncludeFileContent(FBuffer.FileName, IncludeName, Content, FileName) then
  begin
    Content := Content + #13#10;

    New(NewBuffer);
    NewBuffer.SharedBuffer := False;
    NewBuffer.Next := FBuffer;
    NewBuffer.LineNumber := 0;
    NewBuffer.LinePos := 0;
    NewBuffer.Run := 0;
    NewBuffer.FileName := FileName;
    GetMem(NewBuffer.Buf, (Length(Content) + 1) * SizeOf(Char));
    StrPCopy(NewBuffer.Buf, Content);
    NewBuffer.Buf[Length(Content)] := #0;

    FBuffer := NewBuffer;
  end;

  Next;
end;

procedure TmwBasePasLex.Init;
begin
  FCommentState := csNo;
  FBuffer.LineNumber := 0;
  FBuffer.LinePos := 0;
  FBuffer.Run := 0;
end;

procedure TmwBasePasLex.InitFrom(ALexer: TmwBasePasLex);
begin
  SetSharedBuffer(ALexer.FBuffer);
  FCommentState := ALexer.FCommentState;
  FScopedEnums := ALexer.ScopedEnums;
  FBuffer.Run := ALexer.RunPos;
  FTokenID := ALexer.TokenID;
  FExID := ALexer.ExID;
  CloneDefinesFrom(ALexer);
end;

procedure TmwBasePasLex.InitDefinesDefinedByCompiler;
begin
  //Set up the defines that are defined by the compiler
  {$IFDEF VER90}
  AddDefine('VER90'); // 2
  {$ENDIF}
  {$IFDEF VER100}
  AddDefine('VER100'); // 3
  {$ENDIF}
  {$IFDEF VER120}
  AddDefine('VER120'); // 4
  {$ENDIF}
  {$IFDEF VER130}
  AddDefine('VER130'); // 5
  {$ENDIF}
  {$IFDEF VER140} // 6
  AddDefine('VER140');
  {$ENDIF}
  {$IFDEF VER150} // 7/7.1
  AddDefine('VER150');
  {$ENDIF}
  {$IFDEF VER160} // 8
  AddDefine('VER160');
  {$ENDIF}
  {$IFDEF VER170} // 2005
  AddDefine('VER170');
  {$ENDIF}
  {$IFDEF VER180} // 2007
  AddDefine('VER180');
  {$ENDIF}
  {$IFDEF VER185} // 2007
  AddDefine('VER185');
  {$ENDIF}
  {$IFDEF VER190} // 2007.NET
  AddDefine('VER190');
  {$ENDIF}
  {$IFDEF CONDITIONALEXPRESSIONS}
    {$IF COMPILERVERSION > 19.0}
    AddDefine('VER' + IntToStr(Round(10*CompilerVersion)));
    {$IFEND}
  {$ENDIF}
  {$IFDEF WIN32}
  AddDefine('WIN32');
  {$ENDIF}
  {$IFDEF WIN64}
  AddDefine('WIN64');
  {$ENDIF}
  {$IFDEF LINUX}
  AddDefine('LINUX');
  {$ENDIF}
  {$IFDEF LINUX32}
  AddDefine('LINUX32');
  {$ENDIF}
  {$IFDEF LINUX64}
  AddDefine('LINUX64');
  {$ENDIF}
  {$IFDEF POSIX}
  AddDefine('POSIX');
  {$ENDIF}
  {$IFDEF POSIX32}
  AddDefine('POSIX32');
  {$ENDIF}
  {$IFDEF POSIX64}
  AddDefine('POSIX64');
  {$ENDIF}
  {$IFDEF CPUARM}
  AddDefine('CPUARM');
  {$ENDIF}
  {$IFDEF CPUARM32}
  AddDefine('CPUARM32');
  {$ENDIF}
  {$IFDEF CPUARM64}
  AddDefine('CPUARM64');
  {$ENDIF}
  {$IFDEF CPU386}
  AddDefine('CPU386');
  {$ENDIF}
  {$IFDEF CPUX86}
  AddDefine('CPUX86');
  {$ENDIF}
  {$IFDEF CPUX64}
  AddDefine('CPUX64');
  {$ENDIF}
  {$IFDEF CPU32BITS}
  AddDefine('CPU32BITS');
  {$ENDIF}
  {$IFDEF CPU64BITS}
  AddDefine('CPU64BITS');
  {$ENDIF}
  {$IFDEF MSWINDOWS}
  AddDefine('MSWINDOWS');
  {$ENDIF}
  {$IFDEF MACOS}
  AddDefine('MACOS');
  {$ENDIF}
  {$IFDEF MACOS32}
  AddDefine('MACOS32');
  {$ENDIF}
  {$IFDEF MACOS64}
  AddDefine('MACOS64');
  {$ENDIF}
  {$IFDEF IOS}
  AddDefine('IOS');
  {$ENDIF}
  {$IFDEF IOS32}
  AddDefine('IOS32');
  {$ENDIF}
  {$IFDEF IOS64}
  AddDefine('IOS64');
  {$ENDIF}
  {$IFDEF ANDROID}
  AddDefine('ANDROID');
  {$ENDIF}
  {$IFDEF ANDROID32}
  AddDefine('ANDROID32');
  {$ENDIF}
  {$IFDEF ANDROID64}
  AddDefine('ANDROID64');
  {$ENDIF}
  {$IFDEF CONSOLE}
  AddDefine('CONSOLE');
  {$ENDIF}
  {$IFDEF NATIVECODE}
  AddDefine('NATIVECODE');
  {$ENDIF}
  {$IFDEF CONDITIONALEXPRESSIONS}
  AddDefine('CONDITIONALEXPRESSIONS');
  {$ENDIF}
  {$IFDEF UNICODE}
  AddDefine('UNICODE');
  {$ENDIF}
  {$IFDEF ALIGN_STACK}
  AddDefine('ALIGN_STACK');
  {$ENDIF}
  {$IFDEF ARM_NO_VFP_USE}
  AddDefine('ARM_NO_VFP_USE');
  {$ENDIF}
  {$IFDEF ASSEMBLER}
  AddDefine('ASSEMBLER');
  {$ENDIF}
  {$IFDEF AUTOREFCOUNT}
  AddDefine('AUTOREFCOUNT');
  {$ENDIF}
  {$IFDEF EXTERNALLINKER}
  AddDefine('EXTERNALLINKER');
  {$ENDIF}
  {$IFDEF ELF}
  AddDefine('ELF');
  {$ENDIF}
  {$IFDEF MANAGED_RECORD}
  AddDefine('MANAGED_RECORD');
  {$ENDIF}
  {$IFDEF NEXTGEN}
  AddDefine('NEXTGEN');
  {$ENDIF}
  {$IFDEF PC_MAPPED_EXCEPTIONS}
  AddDefine('PC_MAPPED_EXCEPTIONS');
  {$ENDIF}
  {$IFDEF PIC}
  AddDefine('PIC');
  {$ENDIF}
  {$IFDEF UNDERSCOREIMPORTNAME}
  AddDefine('UNDERSCOREIMPORTNAME');
  {$ENDIF}
  {$IFDEF WEAKREF}
  AddDefine('WEAKREF');
  {$ENDIF}
  {$IFDEF WEAKINSTREF}
  AddDefine('WEAKINSTREF');
  {$ENDIF}
  {$IFDEF WEAKINTFREF}
  AddDefine('WEAKINTFREF');
  {$ENDIF}
end;

function TmwBasePasLex.GetStringContent: string;
var
  TempString: string;
  sEnd: Integer;
begin
  if TokenID <> ptStringConst then
    Result := ''
  else
  begin
    TempString := Token;
    sEnd := Length(TempString);
    if TempString[sEnd] <> #39 then Inc(sEnd);
    Result := Copy(TempString, 2, sEnd - 2);
    TempString := '';
  end;
end;

function TmwBasePasLex.GetIsOrdIdent: Boolean;
begin
  if FTokenID = ptIdentifier then
    Result := FExID in [ptBoolean, ptByte, ptChar, ptDWord, ptInt64, ptInteger,
      ptLongInt, ptLongWord, ptPChar, ptShortInt, ptSmallInt, ptWideChar, ptWord]
  else
    Result := False;
end;

function TmwBasePasLex.GetIsOrdinalType: Boolean;
begin
  Result := GetIsOrdIdent or (FTokenID in [ptAsciiChar, ptIntegerConst]);
end;

function TmwBasePasLex.GetIsRealType: Boolean;
begin
  if FTokenID = ptIdentifier then
    Result := FExID in [ptComp, ptCurrency, ptDouble, ptExtended, ptReal, ptReal48, ptSingle]
  else
    Result := False;
end;

function TmwBasePasLex.GetIsStringType: Boolean;
begin
  if FTokenID = ptIdentifier then
    Result := FExID in [ptAnsiString, ptWideString]
  else
    Result := FTokenID in [ptString, ptStringConst];
end;

function TmwBasePasLex.GetIsVariantType: Boolean;
begin
  if FTokenID = ptIdentifier then
    Result := FExID in [ptOleVariant, ptVariant]
  else
    Result := False;
end;

function TmwBasePasLex.GetOrigin: string;
begin
  Result := FBuffer.Buf;
end;

function TmwBasePasLex.GetIsAddOperator: Boolean;
begin
  Result := FTokenID in [ptMinus, ptOr, ptPlus, ptXor];
end;

function TmwBasePasLex.GetIsMulOperator: Boolean;
begin
  Result := FTokenID in [ptAnd, ptAs, ptDiv, ptMod, ptShl, ptShr, ptSlash, ptStar];
end;

function TmwBasePasLex.GetIsRelativeOperator: Boolean;
begin
  Result := FTokenID in [ptAs, ptEqual, ptGreater, ptGreaterEqual, ptLower, ptLowerEqual,
    ptIn, ptIs, ptNotEqual];
end;

function TmwBasePasLex.GetIsCompilerDirective: Boolean;
begin
  Result := FTokenID in [ptCompDirect, ptDefineDirect, ptElseDirect,
    ptEndIfDirect, ptIfDefDirect, ptIfNDefDirect, ptIfOptDirect,
    ptIncludeDirect, ptResourceDirect, ptScopedEnumsDirect, ptUndefDirect];
end;

function TmwBasePasLex.GetGenID: TptTokenKind;
begin
  if (FTokenID <> ptIdentifier) or (FExID = ptUnknown) then
    Result := FTokenID
  else
    Result := FExID;
end;

{ TmwPasLex }

constructor TmwPasLex.Create;
begin
  inherited Create;
  FAheadLex := TmwBasePasLex.Create;
end;

destructor TmwPasLex.Destroy;
begin
  FAheadLex.Free;
  inherited Destroy;
end;

procedure TmwPasLex.AheadNext;
begin
  FAheadLex.NextNoJunk;
end;

function TmwPasLex.GetAheadExID: TptTokenKind;
begin
  Result := FAheadLex.ExID;
end;

function TmwPasLex.GetAheadGenID: TptTokenKind;
begin
  Result := FAheadLex.GenID;
end;

function TmwPasLex.GetAheadToken: string;
begin
  Result := FAheadLex.Token;
end;

function TmwPasLex.GetAheadTokenID: TptTokenKind;
begin
  Result := FAheadLex.TokenID;
end;

procedure TmwPasLex.InitAhead;
begin
  FAheadLex.FCommentState := FCommentState;
  FAheadLex.CloneDefinesFrom(Self);

  FAheadLex.SetSharedBuffer(FBuffer);

  while FAheadLex.IsJunk do
    FAheadLex.Next;
end;

procedure TmwPasLex.SetOrigin(const NewValue: string);
begin
  inherited SetOrigin(NewValue);
  FAheadLex.SetSharedBuffer(FBuffer);
end;

procedure TmwBasePasLex.StringDQProc;
var
  Buffer: PBufferRec;
begin
  if not FAsmCode then
  begin
    SymbolProc;
    Exit;
  end;
  FTokenID := ptStringDQConst;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
    case Buffer.Buf[Buffer.Run] of
      #0, #10, #13:
        begin
          if Assigned(FOnMessage) then
            FOnMessage(Self, meError, 'Unterminated string', PosXY.X, PosXY.Y);
          Exit;
        end;
      '\':
        begin
          Inc(Buffer.Run);
          if CharInSet(Buffer.Buf[Buffer.Run], [#32..#127]) then Inc(Buffer.Run);
        end;
    end;
  until Buffer.Buf[Buffer.Run] = '"';
  Inc(Buffer.Run);
end;

procedure TmwBasePasLex.AmpersandOpProc;
var
  Buffer: PBufferRec;
begin
  FTokenID := ptIdentifier;
  Buffer := FBuffer;
  repeat
    Inc(Buffer.Run);
  until not CharInSet(Buffer.Buf[Buffer.Run], ['a'..'z', 'A'..'Z','0'..'9', '_', '&']);
end;

procedure TmwBasePasLex.UpdateScopedEnums;
begin
  FScopedEnums := SameText(DirectiveParam, 'ON');
end;

initialization
  MakeIdentTable;
end.
