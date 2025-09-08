package ast

interface ASTVisitor {
    // Crate
    fun visitCrate(node: CrateNode)

    // Item
    fun visitFunctionItem(node: FunctionItemNode)
    fun visitStructItem(node: StructItemNode)
    fun visitEnumItem(node: EnumItemNode)
    fun visitConstantItem(node: ConstantItemNode)
    fun visitTraitItem(node: TraitItemNode)
    fun visitImplItem(node: ImplItemNode)

    // Stmt
    fun visitEmptyStmt(node: EmptyStmtNode)
    fun visitItemStmt(node: ItemStmtNode)
    fun visitLetStmt(node: LetStmtNode)
    fun visitExprStmt(node: ExprStmtNode)

    // Type
    fun visitTypePath(node: TypePathNode)
    fun visitReferenceType(node: ReferenceTypeNode)
    fun visitArrayType(node: ArrayTypeNode)
    fun visitUnitType(node: UnitTypeNode)

    // Expr
    fun visitIntLiteralExpr(node: IntLiteralExprNode)
    fun visitCharLiteralExpr(node: CharLiteralExprNode)
    fun visitStringLiteralExpr(node: StringLiteralExprNode)
    fun visitBooleanLiteralExpr(node: BooleanLiteralExprNode)
    fun visitCStringLiteralExpr(node: CStringLiteralExprNode)
    fun visitRawStringLiteralExpr(node: RawStringLiteralExprNode)
    fun visitRawCStringLiteralExpr(node: RawCStringLiteralExprNode)
    fun visitPathExpr(node: PathExprNode)
    fun visitBlockExpr(node: BlockExprNode)
    fun visitBorrowExpr(node: BorrowExprNode)
    fun visitDerefExpr(node: DerefExprNode)
    fun visitNegationExpr(node: NegationExprNode)
    fun visitBinaryExpr(node: BinaryExprNode)
    fun visitComparisonExpr(node: ComparisonExprNode)
    fun visitLazyBooleanExpr(node: LazyBooleanExprNode)
    fun visitTypeCastExpr(node: TypeCastExprNode)
    fun visitAssignExpr(node: AssignExprNode)
    fun visitCompoundAssignExpr(node: CompoundAssignExprNode)
    fun visitGroupedExpr(node: GroupedExprNode)
    fun visitArrayListExpr(node: ArrayListExprNode)
    fun visitArrayLengthExpr(node: ArrayLengthExprNode)
    fun visitIndexExpr(node: IndexExprNode)
    fun visitStructExpr(node: StructExprNode)
    fun visitCallExpr(node: CallExprNode)
    fun visitMethodCallExpr(node: MethodCallExprNode)
    fun visitFieldExpr(node: FieldExprNode)
    fun visitIfExpr(node: IfExprNode)
    fun visitInfiniteLoopExpr(node: InfiniteLoopExprNode)
    fun visitPredicateLoopExpr(node: PredicateLoopExprNode)
    fun visitBreakExpr(node: BreakExprNode)
    fun visitContinueExpr(node: ContinueExprNode)
    fun visitReturnExpr(node: ReturnExprNode)
    fun visitUnderscoreExpr(node: UnderscoreExprNode)

    // Pattern
    fun visitLiteralPattern(node: LiteralPatternNode)
    fun visitIdentifierPattern(node: IdentifierPatternNode)
    fun visitWildcardPattern(node: WildcardPatternNode)
    fun visitReferencePattern(node: ReferencePatternNode)
    fun visitPathPattern(node: PathPatternNode)
}
