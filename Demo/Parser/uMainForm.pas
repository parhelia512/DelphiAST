unit uMainForm;

{$IFDEF FPC}{$MODE Delphi}{$ENDIF}

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, Menus, StdCtrls, ComCtrls, ExtCtrls;

type
  TMainForm = class(TForm)   
    OutputMemo: TMemo;
    MainMenu: TMainMenu;
    OpenDialog: TOpenDialog;
    StatusBar: TStatusBar;    
    CheckBox1: TCheckBox;
    CommentsBox: TListBox;
    Panel1: TPanel;
    Panel2: TPanel;
    Splitter1: TSplitter;
    Label1: TLabel;
    Label2: TLabel;
    OpenDelphiUnit1: TMenuItem;
    ParseDirectory1: TMenuItem;
    File1: TMenuItem;
    FileOpenDialog: TFileOpenDialog;
    procedure OpenDelphiUnit1Click(Sender: TObject);
    procedure ParseDirectory1Click(Sender: TObject);
    procedure CommentsBoxDblClick(Sender: TObject);
  private
    procedure UpdateStatusBarText(const StatusText: string);
    procedure Parse(const FileName: string; UseStringInterning: Boolean);
    procedure ParseDirectory(const DirName: string; UseStringInterning: Boolean);
  end;

var
  MainForm: TMainForm;

implementation

uses
  {$IFNDEF FPC}
    StringUsageLogging, FastMM4,
  {$ENDIF}
  StringPool,
  DelphiAST, DelphiAST.Writer, DelphiAST.Classes,
  SimpleParser.Lexer.Types, IOUtils, Diagnostics,
  DelphiAST.SimpleParserEx,
  StrUtils,
  ShellAPI;

{$IFNDEF FPC}
  {$R *.dfm}
{$ELSE}
  {$R *.lfm}
{$ENDIF}

type
  IIncludeHandlerEx = interface(IIncludeHandler)
    function GetPath: string;
    procedure SetPath(const Path: string);
    property Path: string read GetPath write SetPath;
  end;
  TIncludeHandler = class(TInterfacedObject, IIncludeHandler, IIncludeHandlerEx)
  private
    FPath: string;
    function GetPath: string;
    procedure SetPath(const Path: string);
  public
    constructor Create(const Path: string);
    function GetIncludeFileContent(const ParentFileName, IncludeName: string;
      out Content: string; out FileName: string): Boolean;
  end;

{$IFNDEF FPC}
function MemoryUsed: Cardinal;
 var
   st: TMemoryManagerState;
   sb: TSmallBlockTypeState;
 begin
   GetMemoryManagerState(st);
   Result := st.TotalAllocatedMediumBlockSize + st.TotalAllocatedLargeBlockSize;
   for sb in st.SmallBlockTypeStates do
     Result := Result + sb.UseableBlockSize * sb.AllocatedBlockCount;
end;
{$ELSE}
function MemoryUsed: Cardinal;
begin
  Result := GetFPCHeapStatus.CurrHeapUsed;
end;
{$ENDIF}

procedure TMainForm.Parse(const FileName: string; UseStringInterning: Boolean);
var
  SyntaxTree: TSyntaxNode;
  memused: Cardinal;
  sw: TStopwatch;
  StringPool: TStringPool;
  OnHandleString: TStringEvent;
  Builder: TPasSyntaxTreeBuilder;
  StringStream: TStringStream;
  I: Integer;
begin
  OutputMemo.Clear;
  CommentsBox.Clear;
  Label1.Caption := 'Syntax Tree:';
  Label2.Caption := 'List of Comments:';

  try
    if UseStringInterning then
    begin
      StringPool := TStringPool.Create;
      OnHandleString := StringPool.StringIntern;
    end
    else
    begin
      StringPool := nil;
      OnHandleString := nil;
    end;

    memused := MemoryUsed;
    sw := TStopwatch.StartNew;
    try
      Builder := TPasSyntaxTreeBuilder.Create;
      try
        StringStream := TStringStream.Create;
        try
          StringStream.LoadFromFile(FileName);

          Builder.IncludeHandler := TIncludeHandler.Create(ExtractFilePath(FileName));
          Builder.InitDefinesDefinedByCompiler;
          Builder.OnHandleString := OnHandleString;
          StringStream.Position := 0;

          SyntaxTree := Builder.Run(StringStream);
          try
            OutputMemo.Lines.Text := TSyntaxTreeWriter.ToXML(SyntaxTree, True);
          finally
            SyntaxTree.Free;
          end;
        finally
          StringStream.Free;
        end;

        for I := 0 to Builder.Comments.Count - 1 do
          CommentsBox.Items.Add(Format('[Line: %d, Col: %d] %s',
            [Builder.Comments[I].Line, Builder.Comments[I].Col, Builder.Comments[I].Text]));
      finally
        Builder.Free;
      end
    finally
      if UseStringInterning then
        StringPool.Free;
    end;
    sw.Stop;

    UpdateStatusBarText(Format('Parsed file in %d ms - used memory: %d K',
      [sw.ElapsedMilliseconds, (MemoryUsed - memused) div 1024]));
  except
    on E: ESyntaxTreeException do
      OutputMemo.Lines.Text := Format('[%d, %d] %s', [E.Line, E.Col, E.Message]) + sLineBreak + sLineBreak +
         TSyntaxTreeWriter.ToXML(E.SyntaxTree, True);
  end;
end;

procedure TMainForm.ParseDirectory(const DirName: string; UseStringInterning: Boolean);
var
  SyntaxTree: TSyntaxNode;
  sw: TStopwatch;
  StringPool: TStringPool;
  OnHandleString: TStringEvent;
  Builder: TPasSyntaxTreeBuilder;
  StringStream: TStringStream;
  FileCount: Integer;
  FileName: string;
  IncludeHandler: IIncludeHandlerEx;
begin
  OutputMemo.Clear;
  CommentsBox.Clear;
  Label1.Caption := 'Parsed units:';
  Label2.Caption := 'Errors:';

  if UseStringInterning then
  begin
    StringPool := TStringPool.Create;
    OnHandleString := StringPool.StringIntern;
  end
  else
  begin
    StringPool := nil;
    OnHandleString := nil;
  end;

  FileCount := 0;
  sw := TStopwatch.StartNew;
  try
    Builder := TPasSyntaxTreeBuilder.Create;
    Builder.InitDefinesDefinedByCompiler;
    Builder.OnHandleString := OnHandleString;
    IncludeHandler := TIncludeHandler.Create('');
    Builder.IncludeHandler := IncludeHandler;
    try
      StringStream := TStringStream.Create;
      try
        for FileName in TDirectory.GetFiles(DirName, '*.pas', TSearchOption.soAllDirectories) do
        begin
          Inc(FileCount);
          StringStream.LoadFromFile(FileName);
          StringStream.Position := 0;
          IncludeHandler.Path := ExtractFilePath(FileName);
          if FileCount mod 10 = 0 then
            Application.ProcessMessages;

          SyntaxTree := nil;
          try
            try
              SyntaxTree := Builder.Run(StringStream);
              OutputMemo.Lines.Add(Format('Successfully parsed unit %s', [FileName]));
            except
              on E: ESyntaxTreeException do
                CommentsBox.Items.Add(Format('Error in unit %s [%d, %d] %s', [FileName, E.Line, E.Col, E.Message]));
            end;
          finally
            SyntaxTree.Free;
          end;
        end;
      finally
        StringStream.Free;
      end;
    finally
      Builder.Free;
    end
  finally
    if UseStringInterning then
      StringPool.Free;
  end;
  sw.Stop;

  UpdateStatusBarText(Format('Parsed %d files in %d ms', [FileCount, sw.ElapsedMilliseconds]));
end;

procedure TMainForm.ParseDirectory1Click(Sender: TObject);
begin
  if FileOpenDialog.Execute then
    ParseDirectory(FileOpenDialog.FileName, CheckBox1.Checked);
end;

procedure TMainForm.CommentsBoxDblClick(Sender: TObject);
var
  s: string;
begin
  if CommentsBox.ItemIndex >= 0 then
    s := CommentsBox.Items[CommentsBox.ItemIndex];
  if StartsStr('Error in unit ', s) then
  begin
    s := Copy(s, 15, Pos('[', s) - 16);
    ShellExecute(0, 'OPEN', PChar(s), '', '', SW_SHOWNORMAL);
  end;
end;

procedure TMainForm.OpenDelphiUnit1Click(Sender: TObject);
begin
  if OpenDialog.Execute then
    Parse(OpenDialog.FileName, CheckBox1.Checked);
end;

{ TIncludeHandler }

constructor TIncludeHandler.Create(const Path: string);
begin
  inherited Create;
  FPath := Path;
end;

function TIncludeHandler.GetIncludeFileContent(const ParentFileName, IncludeName: string;
  out Content: string; out FileName: string): Boolean;
begin
  if ParentFileName = '' then
    FileName := TPath.Combine(FPath, IncludeName)
  else
    FileName := TPath.Combine(ExtractFilePath(ParentFileName), IncludeName);
  if not FileExists(FileName) then
    Exit(False);

  Content := TFile.ReadAllText(FileName);
  Result := True;
end;

function TIncludeHandler.GetPath: string;
begin
  Result := FPath;
end;

procedure TIncludeHandler.SetPath(const Path: string);
begin
  FPath := Path;
end;

procedure TMainForm.UpdateStatusBarText(const StatusText: string);
begin
  {$IFDEF FPC}
    StatusBar.SimpleText:= StatusText;
  {$ELSE}
    StatusBar.Panels[0].Text := StatusText;
  {$ENDIF}
end;

end.
