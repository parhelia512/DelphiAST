unit DelphiAST.Classes;

{$IFDEF FPC}{$MODE DELPHI}{$ENDIF}

interface

uses
  SysUtils, Generics.Collections, SimpleParser.Lexer.Types, DelphiAST.Consts;

type
  EParserException = class(Exception)
  strict private
    FFileName: string;
    FLine, FCol: Integer;
  public
    constructor Create(Line, Col: Integer; const FileName, Msg: string); reintroduce;

    property FileName: string read FFileName;
    property Line: Integer read FLine;
    property Col: Integer read FCol;
  end;
  
  TAttributeEntry = TPair<TAttributeName, string>;
  PAttributeEntry = ^TAttributeEntry;

  TSyntaxNodeClass = class of TSyntaxNode;
  TSyntaxNode = class
  private
    FPos: TTokenPoint;
    function GetHasChildren: Boolean;
    function GetHasAttributes: Boolean;
    function TryGetAttributeEntry(const Key: TAttributeName; var AttributeEntry: PAttributeEntry): boolean;
  protected
    FAttributes: TArray<TAttributeEntry>;
    FChildNodes: TArray<TSyntaxNode>;
    FTyp: TSyntaxNodeType;
    FParentNode: TSyntaxNode;
  public
    class var InstanceCount: Integer;
    class function Create(Typ: TSyntaxNodeType): TSyntaxNode; inline;

    class function NewInstance: TObject; override;
    procedure FreeInstance; override;

    function Clone: TSyntaxNode; virtual;
    procedure AssignPositionFrom(const Node: TSyntaxNode); inline;

    function GetAttribute(const Key: TAttributeName): string;
    function HasAttribute(const Key: TAttributeName): Boolean;
    procedure SetAttribute(const Key: TAttributeName; const Value: string);
    procedure ClearAttributes;

    function AddChild(Node: TSyntaxNode): TSyntaxNode; overload;
    function AddChild(Typ: TSyntaxNodeType): TSyntaxNode; overload;
    procedure DeleteChild(Node: TSyntaxNode);
    procedure ExtractChild(Node: TSyntaxNode);
    function FindNode(Typ: TSyntaxNodeType): TSyntaxNode; overload;
    // Searches for a node located along the path from the type of nodes
    // specified in the TypesPath parameter.
    // ntUnknown in the TypesPath parameter means a node of any type.
    // For example, for the branch presented below as XML
    // FindNode([ntAbsolute, ntValue, ntExpression, ntIdentifier]),
    // FindNode([ntAbsolute, ntUnknown, ntExpression, ntIdentifier]) �
    // FindNode([ntAbsolute, ntUnknown, ntUnknown, ntIdentifier])
    // return the IDENTIFIER node.
    // <VARIABLE line="9" col="3">
    //   <NAME line="9" col="3" value="ValueRec"/>
    //   <TYPE line="9" col="13" name="LongInt"/>
    //   <ABSOLUTE line="9" col="21">
    //     <VALUE line="9" col="30">
    //       <EXPRESSION line="9" col="30">
    //         <IDENTIFIER line="9" col="30" name="AValue"/>
    //       </EXPRESSION>
    //     </VALUE>
    //   </ABSOLUTE>
    // </VARIABLE>.
    function FindNode(const TypesPath: array of TSyntaxNodeType): TSyntaxNode; overload;
    property Attributes: TArray<TAttributeEntry> read FAttributes;
    property ChildNodes: TArray<TSyntaxNode> read FChildNodes;
    property HasAttributes: Boolean read GetHasAttributes;
    property HasChildren: Boolean read GetHasChildren;
    property Typ: TSyntaxNodeType read FTyp;
    property ParentNode: TSyntaxNode read FParentNode;

    property Pos: TTokenPoint read FPos write FPos;
    property Col: Integer read FPos.X write FPos.X;
    property Line: Integer read FPos.Y write FPos.Y;
  end;

  TCompoundSyntaxNode = class(TSyntaxNode)
  private
    FEndPos: TTokenPoint;
  public
    function Clone: TSyntaxNode; override;

    property EndPos: TTokenPoint read FEndPos write FEndPos;
    property EndCol: Integer read FEndPos.X write FEndPos.X;
    property EndLine: Integer read FEndPos.Y write FEndPos.Y;
  end;

  TValuedSyntaxNode = class(TSyntaxNode)
  private
    FValue: string;
  public
    procedure FreeInstance; override;

    function Clone: TSyntaxNode; override;

    property Value: string read FValue write FValue;
  end;

  TCommentNode = class(TSyntaxNode)
  private
    FText: string;
  public
    class function Create(Typ: TSyntaxNodeType): TCommentNode; inline;
    procedure FreeInstance; override;

    function Clone: TSyntaxNode; override;

    property Text: string read FText write FText;
  end;

  TExpressionTools = class
  private
    class function CreateNodeWithParentsPosition(NodeType: TSyntaxNodeType; ParentNode: TSyntaxNode): TSyntaxNode;
  public
    class procedure ToReverseNotation(var Expr: TArray<TSyntaxNode>); static;
    class procedure NodeListToTree(const Expr: TArray<TSyntaxNode>; Root: TSyntaxNode); static;
    class function PrepareExpr(const ExprNodes: TArray<TSyntaxNode>): TArray<TSyntaxNode>; static;
    class procedure RawNodeListToTree(const RawNodeList: TArray<TSyntaxNode>; NewRoot: TSyntaxNode; const FileName: string); static;
  end;

implementation

type
  TOperatorKind = (okNone, okUnary, okBinary);
  TOperatorAssocType = (atNone, atLeft, atRight);

  TOperatorInfo = record
    Typ: TSyntaxNodeType;
    Priority: Byte;
    Kind: TOperatorKind;
    AssocType: TOperatorAssocType;
  end;

  TOperators = class
  strict private const
    OperatorsInfo: array [-1..27] of TOperatorInfo =
      ((Typ: ntUnknown;      Priority: 0; Kind: okNone;   AssocType: atNone),
       (Typ: ntAddr;         Priority: 1; Kind: okUnary;  AssocType: atRight),
       (Typ: ntDeref;        Priority: 1; Kind: okUnary;  AssocType: atLeft),
       (Typ: ntGeneric;      Priority: 1; Kind: okBinary; AssocType: atRight),
       (Typ: ntIndexed;      Priority: 1; Kind: okUnary;  AssocType: atLeft),
       (Typ: ntDot;          Priority: 2; Kind: okBinary; AssocType: atRight),
       (Typ: ntCall;         Priority: 3; Kind: okBinary; AssocType: atRight),
       (Typ: ntUnaryMinus;   Priority: 5; Kind: okUnary;  AssocType: atRight),
       (Typ: ntNot;          Priority: 6; Kind: okUnary;  AssocType: atRight),
       (Typ: ntMul;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntFDiv;         Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntDiv;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntMod;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntAnd;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntShl;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntShr;          Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntAs;           Priority: 7; Kind: okBinary; AssocType: atRight),
       (Typ: ntAdd;          Priority: 8; Kind: okBinary; AssocType: atRight),
       (Typ: ntSub;          Priority: 8; Kind: okBinary; AssocType: atRight),
       (Typ: ntOr;           Priority: 8; Kind: okBinary; AssocType: atRight),
       (Typ: ntXor;          Priority: 8; Kind: okBinary; AssocType: atRight),
       (Typ: ntEqual;        Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntNotEqual;     Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntLower;        Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntGreater;      Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntLowerEqual;   Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntGreaterEqual; Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntIn;           Priority: 9; Kind: okBinary; AssocType: atRight),
       (Typ: ntIs;           Priority: 9; Kind: okBinary; AssocType: atRight));
  class var
    OperatorsMapping: array[TSyntaxNodeType] of ShortInt;
    class function GetItem(Typ: TSyntaxNodeType): TOperatorInfo; static; inline;
  private
    class procedure Initialize; static;
  public
    class property Items[Typ: TSyntaxNodeType]: TOperatorInfo read GetItem; default;
  end;

  TNodeStack = array[0..MaxInt div SizeOf(TSyntaxNode) - 1] of TSyntaxNode;
  PNodeStack = ^TNodeStack;

class procedure TOperators.Initialize;
var
  i: Integer;
begin
  FillChar(OperatorsMapping, Length(OperatorsMapping), -1);
  for i := 0 to High(OperatorsInfo) do
    OperatorsMapping[OperatorsInfo[i].Typ] := i;
end;

class function TOperators.GetItem(Typ: TSyntaxNodeType): TOperatorInfo;
begin
  Result := OperatorsInfo[OperatorsMapping[Typ]];
end;

class procedure TExpressionTools.ToReverseNotation(var Expr: TArray<TSyntaxNode>);
var
  StackBuffer: array[0..1023] of TSyntaxNode;
  Stack: PNodeStack;
  Node, StackNode: TSyntaxNode;
  i, StackCount, Count: Integer;
  OpInfo, OpInfo2: TOperatorInfo;
begin
  StackCount := Length(Expr);
  if StackCount > Length(StackBuffer) then
    GetMem(Stack, StackCount * SizeOf(TSyntaxNode))
  else
    Stack := @StackBuffer;
  StackCount := 0;
  Count := 0;
  try
    for i := 0 to High(Expr) do
    begin
      Node := Expr[i];
      OpInfo := TOperators.Items[Node.Typ];
      if OpInfo.Kind <> okNone then
      begin
        while StackCount > 0 do
        begin
          StackNode := Stack[StackCount-1];
          OpInfo2 := TOperators.Items[StackNode.Typ];
          if OpInfo2.Kind = okNone then Break;
          case OpInfo.AssocType of
            atLeft:  if OpInfo.Priority < OpInfo2.Priority then Break;
            atRight: if OpInfo.Priority <= OpInfo2.Priority then Break;
          end;
          Dec(StackCount);
          Expr[Count] := StackNode;
          Inc(Count);
        end;

        Stack[StackCount] := Node;
        Inc(StackCount);
      end else
        case Node.Typ of
          ntRoundOpen:
          begin
            Stack[StackCount] := Node;
            Inc(StackCount);
          end;
          ntRoundClose:
          begin
            while True do
            begin
              StackNode := Stack[StackCount-1];
              if StackNode.Typ = ntRoundOpen then Break;
              Dec(StackCount);
              Expr[Count] := StackNode;
              Inc(Count);
            end;

            // RoundOpen and RoundClose nodes are not needed anymore
            Dec(StackCount);
            Stack[StackCount].FreeInstance;
            Node.FreeInstance;

            if StackCount > 0 then
            begin
              StackNode := Stack[StackCount-1];
              OpInfo := TOperators.Items[StackNode.Typ];
              if OpInfo.Kind <> okNone then
              begin
                Dec(StackCount);
                Expr[Count] := StackNode;
                Inc(Count);
              end;
            end;
          end;
        else
          Expr[Count] := Node;
          Inc(Count);
        end;
    end;

    while StackCount > 0 do
    begin
      Dec(StackCount);
      Expr[Count] := Stack[StackCount];
      Inc(Count);
    end;
  finally
    if Stack <> @StackBuffer[0] then
      FreeMem(Stack);
  end;
  SetLength(Expr, Count);
end;

class procedure TExpressionTools.NodeListToTree(const Expr: TArray<TSyntaxNode>; Root: TSyntaxNode);
var
  StackBuffer: array[0..1023] of TSyntaxNode;
  Stack: PNodeStack;
  StackCount: Integer;
  Node: TSyntaxNode;
  i: Integer;
begin
  StackCount := Length(Expr);
  if StackCount > Length(StackBuffer) then
    GetMem(Stack, StackCount * SizeOf(TSyntaxNode))
  else
    Stack := @StackBuffer;
  StackCount := 0;
  try
    for i := 0 to High(Expr) do
    begin
      Node := Expr[i];
      case TOperators.Items[Node.Typ].Kind of
        okUnary:
        begin
          Dec(StackCount);
          Node.AddChild(Stack[StackCount]);
        end;
        okBinary:
        begin
          Dec(StackCount, 2);
          Node.AddChild(Stack[StackCount]);
          Node.AddChild(Stack[StackCount + 1]);
        end;
      end;
      Stack[StackCount] := Node;
      Inc(StackCount);
    end;

    Dec(StackCount);
    Root.AddChild(Stack[StackCount]);

    Assert(StackCount = 0);
  finally
    if Stack <> @StackBuffer[0] then
      FreeMem(Stack);
  end;
end;

class function TExpressionTools.PrepareExpr(const ExprNodes: TArray<TSyntaxNode>): TArray<TSyntaxNode>;
const
  NodeTypes: array[Boolean] of TSyntaxNodeType = (ntCall, ntGeneric);
var
  Node, PrevNode: TSyntaxNode;
  i, Count: NativeInt;
  OpInfo: TOperatorInfo;
  NodeType: TSyntaxNodeType;
begin
  SetLength(Result, Length(ExprNodes) * 2);
  Count := 0;

  PrevNode := nil;
  for i := 0 to High(ExprNodes) do
  begin
    Node := ExprNodes[i];
    if Node.Typ in [ntCall, ntAlignmentParam] then
      Continue;

    if Assigned(PrevNode) and (Node.Typ in [ntRoundOpen, ntTypeArgs]) then
    begin
      NodeType := NodeTypes[Node.Typ = ntTypeArgs];
      OpInfo := TOperators.Items[PrevNode.Typ];
      case OpInfo.Kind of
        okNone:
          if PrevNode.Typ <> Node.Typ then
          begin
            Result[Count] := CreateNodeWithParentsPosition(NodeType, Node.ParentNode);
            Inc(Count);
          end;
        okUnary:
          if OpInfo.AssocType = atLeft then
          begin
            Result[Count] := CreateNodeWithParentsPosition(NodeType, Node.ParentNode);
            Inc(Count);
          end;
      end;
    end;

    Result[Count] := Node.Clone;
    Inc(Count);
    PrevNode := Node;
  end;
  SetLength(Result, Count);
end;

class function TExpressionTools.CreateNodeWithParentsPosition(NodeType: TSyntaxNodeType; ParentNode: TSyntaxNode): TSyntaxNode;
begin
  Result := TSyntaxNode.Create(NodeType);
  Result.Col := ParentNode.Col;
  Result.Line := ParentNode.Line;
end;

class procedure TExpressionTools.RawNodeListToTree(
  const RawNodeList: TArray<TSyntaxNode>; NewRoot: TSyntaxNode; const FileName: string);
var
  Nodes: TArray<TSyntaxNode>;
begin
  try
    Nodes := PrepareExpr(RawNodeList);
    ToReverseNotation(Nodes);
    NodeListToTree(Nodes, NewRoot);
  except
    on E: Exception do
      raise EParserException.Create(NewRoot.Line, NewRoot.Col, FileName, E.Message);
  end;
end;

{ TSyntaxNode }

procedure TSyntaxNode.SetAttribute(const Key: TAttributeName; const Value: string);
var
  AttributeEntry: PAttributeEntry;
  len: Integer;
begin
  if not TryGetAttributeEntry(Key, AttributeEntry) then
  begin
    // TODO: check if overallocation (which the memory manager does anyway) increases performance
    len := Length(FAttributes);
    SetLength(FAttributes, len + 1);
    AttributeEntry := @FAttributes[len];
    AttributeEntry^.Key := Key;
  end;
  AttributeEntry^.Value := Value;
end;

function TSyntaxNode.TryGetAttributeEntry(const Key: TAttributeName; var AttributeEntry: PAttributeEntry): boolean;
var
  i: integer;
begin
  for i := 0 to High(FAttributes) do
    if FAttributes[i].Key = Key then
    begin
      AttributeEntry := @FAttributes[i];
      Exit(True);
    end;

  Result := False;
end;

function TSyntaxNode.AddChild(Node: TSyntaxNode): TSyntaxNode;
var
  len: Integer;
begin
  Assert(Assigned(Node));

  len := Length(FChildNodes);
  SetLength(FChildNodes, len + 1);
  FChildNodes[len] := Node;

  Node.FParentNode := Self;

  Result := Node;
end;

function TSyntaxNode.AddChild(Typ: TSyntaxNodeType): TSyntaxNode;
begin
  Result := AddChild(TSyntaxNode.Create(Typ));
end;

function TSyntaxNode.Clone: TSyntaxNode;
var
  i: Integer;
begin
  Result := TSyntaxNodeClass(Self.ClassType).Create(FTyp);

  SetLength(Result.FChildNodes, Length(FChildNodes));
  for i := 0 to High(FChildNodes) do
  begin
    Result.FChildNodes[i] := FChildNodes[i].Clone;
    Result.FChildNodes[i].FParentNode := Result;
  end;

  Result.FAttributes := Copy(FAttributes);
  Result.Pos := FPos;
end;

class function TSyntaxNode.Create(Typ: TSyntaxNodeType): TSyntaxNode;
begin
  Inc(InstanceCount);
  Result := TSyntaxNode(NewInstance);
  Result.FTyp := Typ;
end;

procedure TSyntaxNode.ExtractChild(Node: TSyntaxNode);
var
  i: integer;
begin
  for i := 0 to High(FChildNodes) do
    if FChildNodes[i] = Node then
    begin
      if i < High(FChildNodes) then
        Move(FChildNodes[i + 1], FChildNodes[i], SizeOf(TSyntaxNode) * (Length(FChildNodes) - i - 1));
      SetLength(FChildNodes, High(FChildNodes));
      Break;
    end;
end;

procedure TSyntaxNode.DeleteChild(Node: TSyntaxNode);
begin
  ExtractChild(Node);
  Node.Free;
end;

function TSyntaxNode.FindNode(Typ: TSyntaxNodeType): TSyntaxNode;
var
  i: Integer;
begin
  for i := 0 to High(FChildNodes) do
    if FChildNodes[i].Typ = Typ then
      Exit(FChildNodes[i]);
  Result := nil;
end;

function TSyntaxNode.FindNode(const TypesPath: array of TSyntaxNodeType): TSyntaxNode;

  function FindNodeRecursively(Node: TSyntaxNode;
    const TypesPath: array of TSyntaxNodeType; TypeIndex: Integer): TSyntaxNode;
  var
    ChildNode: TSyntaxNode;
    i: NativeInt;
  begin
    Result := nil;
    for i := 0 to High(Node.ChildNodes) do
    begin
      ChildNode := Node.ChildNodes[i];
      if TypesPath[TypeIndex] in [ChildNode.Typ] + [ntUnknown] then
      begin
        if TypeIndex < High(TypesPath) then
          Result := FindNodeRecursively(ChildNode, TypesPath, TypeIndex + 1)
        else
          Result := ChildNode;
        if Assigned(Result) then
          Exit;
      end;
    end;
  end;

begin
  if TypesPath[High(TypesPath)] <> ntUnknown then
    Result := FindNodeRecursively(Self, TypesPath, Low(TypesPath))
  else
    Result := nil;
end;

procedure TSyntaxNode.FreeInstance;
var
  i: integer;
begin
  for i := 0 to High(FChildNodes) do
    FChildNodes[i].FreeInstance;
  FChildNodes := nil;
  FAttributes := nil;
  FreeMem(Pointer(Self));
end;

function TSyntaxNode.GetAttribute(const Key: TAttributeName): string;
var
  AttributeEntry: PAttributeEntry;
begin
  if TryGetAttributeEntry(Key, AttributeEntry) then
    Result := AttributeEntry^.Value
  else
    Result := '';
end;

function TSyntaxNode.GetHasAttributes: Boolean;
begin
  Result := Length(FAttributes) > 0;
end;

function TSyntaxNode.GetHasChildren: Boolean;
begin
  Result := Length(FChildNodes) > 0;
end;

function TSyntaxNode.HasAttribute(const Key: TAttributeName): Boolean;
var
  AttributeEntry: PAttributeEntry;
begin
  Result := TryGetAttributeEntry(Key, AttributeEntry);
end;

class function TSyntaxNode.NewInstance: TObject;
var
  cls: PByte;
begin
  cls := Pointer(Self);
  Result := AllocMem(PInteger(@cls[vmtInstanceSize])^);
  PPointer(Result)^ := cls;
end;

procedure TSyntaxNode.ClearAttributes;
begin
  SetLength(FAttributes, 0);
end;

procedure TSyntaxNode.AssignPositionFrom(const Node: TSyntaxNode);
begin
  FPos := Node.Pos;
end;

{ TCompoundSyntaxNode }

function TCompoundSyntaxNode.Clone: TSyntaxNode;
begin
  Result := inherited;

  TCompoundSyntaxNode(Result).EndPos := FEndPos;
end;

{ TValuedSyntaxNode }

function TValuedSyntaxNode.Clone: TSyntaxNode;
begin
  Result := inherited;

  TValuedSyntaxNode(Result).Value := Self.Value;
end;

procedure TValuedSyntaxNode.FreeInstance;
begin
  FValue := '';
  inherited;
end;

{ TCommentNode }

function TCommentNode.Clone: TSyntaxNode;
begin
  Result := inherited;

  TCommentNode(Result).Text := Self.Text;
end;

class function TCommentNode.Create(Typ: TSyntaxNodeType): TCommentNode;
begin
  Result := TCommentNode(NewInstance);
  Result.FTyp := Typ;
end;

procedure TCommentNode.FreeInstance;
begin
  FText := '';
  inherited;
end;

{ EParserException }

constructor EParserException.Create(Line, Col: Integer; const FileName, Msg: string);
begin
  inherited Create(Msg);
  FFileName := FileName;
  FLine := Line;
  FCol := Col;
end;

initialization
  TOperators.Initialize;

end.
