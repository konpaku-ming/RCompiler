package ast

enum class NodeType {
    Crate,
    FunctionItem, StructItem, EnumItem, ConstantItem, TraitItem, ImplItem,
    EmptyStmt, ItemStmt, LetStmt, ExprStmt,
    TypePath, ReferenceType, ArrayType, UnitType,
    IntLiteralExpr, CharLiteralExpr, StringLiteralExpr, BooleanLiteralExpr,
    CStringLiteralExpr, RawStringLiteralExpr, RawCStringLiteralExpr,
    PathExpr, GroupedExpr, BlockExpr, BorrowExpr, DerefExpr,
    NegationExpr, BinaryExpr, ComparisonExpr, LazyBooleanExpr, TypeCastExpr,
    AssignExpr, CompoundAssignExpr,
    ArrayList, ArrayLength, IndexExpr,
    StructExpr, CallExpr, MethodCallExpr, FieldExpr,
    InfiniteLoopExpr, PredicateLoopExpr, BreakExpr, ContinueExpr, IfExpr,
    ReturnExpr, UnderscoreExpr,
    LiteralPattern, IdentifierPattern, WildcardPattern, ReferencePattern, PathPattern,
}

sealed class ASTNode {
    abstract val type: NodeType
    abstract fun accept(visitor: ASTVisitor)
}

data class CrateNode(
    val items: List<ItemNode>
) : ASTNode() {
    override val type: NodeType = NodeType.Crate

    override fun accept(visitor: ASTVisitor) {
        visitor.visitCrate(this)
    }
}

// Item
sealed class ItemNode : ASTNode()

data class SelfParam(
    val isMut: Boolean,
    val isRef: Boolean,
    val selfType: TypeNode?
)

data class FunctionParam(
    val paramPattern: PatternNode,
    val type: TypeNode
)

data class FunctionItemNode(
    val isConst: Boolean,
    val fnName: Token,
    val selfParam: SelfParam?,
    val params: List<FunctionParam>,
    val returnType: TypeNode?,
    val body: BlockExprNode?
) : ItemNode() {
    override val type: NodeType = NodeType.FunctionItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitFunctionItem(this)
    }
}

data class StructField(
    val name: Token,
    val type: TypeNode
)

data class StructItemNode(
    val structName: Token,
    val fields: List<StructField>?,
) : ItemNode() {
    override val type: NodeType = NodeType.StructItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitStructItem(this)
    }
}

data class EnumItemNode(
    val enumName: Token,
    val variants: List<Token>
) : ItemNode() {
    override val type: NodeType = NodeType.EnumItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitEnumItem(this)
    }
}

data class ConstantItemNode(
    val constantName: Token,
    val constantType: TypeNode,
    val value: ExprNode?
) : ItemNode() {
    override val type: NodeType = NodeType.ConstantItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitConstantItem(this)
    }
}

data class TraitItemNode(
    val traitName: Token,
    val items: List<ItemNode>
) : ItemNode() {
    override val type: NodeType = NodeType.TraitItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitTraitItem(this)
    }
}

data class ImplItemNode(
    val traitName: Token?,
    val implType: TypeNode,
    val methods: List<ItemNode>
) : ItemNode() {
    override val type: NodeType = NodeType.ImplItem

    override fun accept(visitor: ASTVisitor) {
        visitor.visitImplItem(this)
    }
}

// Stmt
sealed class StmtNode : ASTNode()

data class EmptyStmtNode(
    val semicolon: Token,
) : StmtNode() {
    override val type: NodeType = NodeType.EmptyStmt

    override fun accept(visitor: ASTVisitor) {
        visitor.visitEmptyStmt(this)
    }
}

data class ItemStmtNode(
    val item: ItemNode,
) : StmtNode() {
    override val type: NodeType = NodeType.ItemStmt

    override fun accept(visitor: ASTVisitor) {
        visitor.visitItemStmt(this)
    }
}

data class LetStmtNode(
    val pattern: PatternNode,
    val valueType: TypeNode,
    val value: ExprNode?
) : StmtNode() {
    override val type: NodeType = NodeType.LetStmt

    override fun accept(visitor: ASTVisitor) {
        visitor.visitLetStmt(this)
    }
}

data class ExprStmtNode(
    val expr: ExprNode,
    val hasSemicolon: Boolean,
) : StmtNode() {
    override val type: NodeType = NodeType.ExprStmt

    override fun accept(visitor: ASTVisitor) {
        visitor.visitExprStmt(this)
    }
}

// Type
sealed class TypeNode : ASTNode()

data class PathSegment(
    val identSegment: Token,
)

data class TypePathNode(
    val path: PathSegment,
) : TypeNode() {
    override val type: NodeType = NodeType.TypePath

    override fun accept(visitor: ASTVisitor) {
        visitor.visitTypePath(this)
    }
}

data class ReferenceTypeNode(
    val isMut: Boolean,
    val tar: TypeNode
) : TypeNode() {
    override val type: NodeType = NodeType.ReferenceType

    override fun accept(visitor: ASTVisitor) {
        visitor.visitReferenceType(this)
    }
}

data class ArrayTypeNode(
    val elementType: TypeNode,
    val length: ExprNode
) : TypeNode() {
    override val type: NodeType = NodeType.ArrayType

    override fun accept(visitor: ASTVisitor) {
        visitor.visitArrayType(this)
    }
}

class UnitTypeNode() : TypeNode() {
    override val type: NodeType = NodeType.UnitType

    override fun accept(visitor: ASTVisitor) {
        visitor.visitUnitType(this)
    }
}

// Expr
sealed class ExprNode : ASTNode()
sealed class ExprWithoutBlockNode : ExprNode()
sealed class ExprWithBlockNode : ExprNode()

sealed class LiteralExprNode() : ExprWithoutBlockNode()

data class IntLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.IntLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitIntLiteralExpr(this)
    }
}

data class CharLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.CharLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitCharLiteralExpr(this)
    }
}

data class StringLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.StringLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitStringLiteralExpr(this)
    }
}

data class BooleanLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.BooleanLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitBooleanLiteralExpr(this)
    }
}

data class CStringLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.CStringLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitCStringLiteralExpr(this)
    }
}

data class RawStringLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.RawStringLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitRawStringLiteralExpr(this)
    }
}

data class RawCStringLiteralExprNode(
    val raw: String
) : LiteralExprNode() {
    override val type: NodeType = NodeType.RawCStringLiteralExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitRawCStringLiteralExpr(this)
    }
}

data class PathExprNode(
    val path: List<PathSegment>,
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.PathExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitPathExpr(this)
    }
}

data class BlockExprNode(
    val statements: List<StmtNode>, //may be empty
    val expr: ExprNode?
) : ExprWithBlockNode() {
    override val type: NodeType = NodeType.BlockExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitBlockExpr(this)
    }
}

sealed class OperatorExprNode : ExprWithoutBlockNode()

data class BorrowExprNode(
    val isMut: Boolean,
    val expr: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.BorrowExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitBorrowExpr(this)
    }
}

data class DerefExprNode(
    val expr: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.DerefExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitDerefExpr(this)
    }
}

data class NegationExprNode(
    val operator: Token,
    val expr: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.NegationExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitNegationExpr(this)
    }
}

data class BinaryExprNode(
    // arithmetic or logical
    val left: ExprNode,
    val operator: Token,
    val right: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.BinaryExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitBinaryExpr(this)
    }
}

data class ComparisonExprNode(
    val left: ExprNode,
    val op: Token,
    val right: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.ComparisonExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitComparisonExpr(this)
    }
}

data class LazyBooleanExprNode(
    val left: ExprNode,
    val op: Token,
    val right: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.LazyBooleanExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitLazyBooleanExpr(this)
    }
}

data class TypeCastExprNode(
    val expr: ExprNode,
    val targetType: TypeNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.TypeCastExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitTypeCastExpr(this)
    }
}

data class AssignExprNode(
    val left: ExprNode,
    val right: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.AssignExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitAssignExpr(this)
    }
}

data class CompoundAssignExprNode(
    val left: ExprNode,
    val op: Token,
    val right: ExprNode
) : OperatorExprNode() {
    override val type: NodeType = NodeType.CompoundAssignExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitCompoundAssignExpr(this)
    }
}

data class GroupedExprNode(
    val expr: ExprNode
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.GroupedExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitGroupedExpr(this)
    }
}

sealed class ArrayExprNode : ExprWithoutBlockNode()

data class ArrayListExprNode(
    val element: List<ExprNode>
) : ArrayExprNode() {
    override val type: NodeType = NodeType.ArrayList

    override fun accept(visitor: ASTVisitor) {
        visitor.visitArrayListExpr(this)
    }
}

data class ArrayLengthExprNode(
    val element: ExprNode,
    val length: ExprNode
) : ArrayExprNode() {
    override val type: NodeType = NodeType.ArrayLength

    override fun accept(visitor: ASTVisitor) {
        visitor.visitArrayLengthExpr(this)
    }
}

data class IndexExprNode(
    val base: ExprNode,
    val index: ExprNode
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.IndexExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitIndexExpr(this)
    }
}

data class StructExprField(
    val name: Token, // must be identifier
    val expr: ExprNode?,
)

data class StructExprNode(
    val path: PathExprNode,
    val fields: List<StructExprField>,
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.StructExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitStructExpr(this)
    }
}

data class CallExprNode(
    val expr: ExprNode,
    val params: List<ExprNode>
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.CallExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitCallExpr(this)
    }
}

data class MethodCallExprNode(
    val expr: ExprNode,
    val method: PathSegment,
    val params: List<ExprNode>
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.MethodCallExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitMethodCallExpr(this)
    }
}

data class FieldExprNode(
    val expr: ExprNode,
    val field: Token // must be identifier
) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.FieldExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitFieldExpr(this)
    }
}

data class Condition(val expr: ExprNode)

enum class ElseType {
    NULL, BLOCK, IF
}

data class IfExprNode(
    val condition: Condition,
    val thenBranch: BlockExprNode,
    val elseType: ElseType,
    val elseBranch: ExprNode?
) : ExprWithBlockNode() {
    override val type: NodeType = NodeType.IfExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitIfExpr(this)
    }
}

sealed class LoopExprNode : ExprWithBlockNode()

data class InfiniteLoopExprNode(
    val block: BlockExprNode
) : LoopExprNode() {
    override val type: NodeType = NodeType.InfiniteLoopExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitInfiniteLoopExpr(this)
    }
}

data class PredicateLoopExprNode(
    val condition: Condition,
    val block: BlockExprNode
) : LoopExprNode() {
    override val type: NodeType = NodeType.PredicateLoopExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitPredicateLoopExpr(this)
    }
}

data class BreakExprNode(val value: ExprNode?) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.BreakExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitBreakExpr(this)
    }
}

class ContinueExprNode() : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.ContinueExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitContinueExpr(this)
    }
}

data class ReturnExprNode(val value: ExprNode?) : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.ReturnExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitReturnExpr(this)
    }
}

class UnderscoreExprNode() : ExprWithoutBlockNode() {
    override val type: NodeType = NodeType.UnderscoreExpr

    override fun accept(visitor: ASTVisitor) {
        visitor.visitUnderscoreExpr(this)
    }
}

sealed class PatternNode : ASTNode()

data class LiteralPatternNode(
    val expr: LiteralExprNode,
    val isNeg: Boolean
) : PatternNode() {
    override val type: NodeType = NodeType.LiteralPattern

    override fun accept(visitor: ASTVisitor) {
        visitor.visitLiteralPattern(this)
    }
}

data class IdentifierPatternNode(
    val name: Token,
    val isRef: Boolean,
    val isMut: Boolean,
) : PatternNode() {
    override val type: NodeType = NodeType.IdentifierPattern

    override fun accept(visitor: ASTVisitor) {
        visitor.visitIdentifierPattern(this)
    }
}

class WildcardPatternNode() : PatternNode() {
    override val type: NodeType = NodeType.WildcardPattern

    override fun accept(visitor: ASTVisitor) {
        visitor.visitWildcardPattern(this)
    }
}

data class ReferencePatternNode(
    val isMut: Boolean,
    val pattern: PatternNode
) : PatternNode() {
    override val type: NodeType = NodeType.ReferencePattern

    override fun accept(visitor: ASTVisitor) {
        visitor.visitReferencePattern(this)
    }
}

data class PathPatternNode(
    val path: PathExprNode
) : PatternNode() {
    override val type: NodeType = NodeType.PathPattern

    override fun accept(visitor: ASTVisitor) {
        visitor.visitPathPattern(this)
    }
}
