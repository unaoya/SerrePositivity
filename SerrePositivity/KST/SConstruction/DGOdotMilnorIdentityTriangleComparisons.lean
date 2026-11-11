module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareFrame
public import SerrePositivity.KST.SConstruction.SquareFrameTriangleComparisons

/-!
概要：恒等実右面の元上下二胞体を、絶対恒等提示の同じ二胞体全体と比較する。
方針：同じ四頂点経路を持つ指定四辺比較を、両端固定の二つの prism へ渡す。
規約：D2 の全比較は明示入力。共有対角の接合と全四角形比較は別工程。
使われ方：右面の VerdierSquareDiagramIso の全二胞体比較の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：元実・絶対上下二単体を同時に端点に保持する比較ホモトピー。
方針：同じ元四境界を使った二短辺 prism を取る。
規約：元両二単体を選び直さない。使われ方：共有対角を合わせる二つの実比較。 -/
def triangleHomotopy (j : Fin 2) : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  squareFrameTriangleHomotopy (squareFrameComparison R d v) j

/-- 概要：同じ元上下二胞体の比較は元実ホモトピーの可逆な辺。
方針：元四側面の可逆性を使う。
規約：元二胞体・元実比較を保持。使われ方：全二胞体比較の同型構造。 -/
lemma triangleHomotopy_isInvertible (j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (triangleHomotopy R d v j)) :=
  squareFrameTriangleHomotopy_isInvertible (squareFrameComparison R d v) j

/-- 概要：元実右面と絶対恒等面の上下二単体全体の指定比較。
方針：同じ元 prism 比較の可逆な辺の類を使う。
規約：上下の共有対角の一致は未主張。使われ方：全右面比較の二つの成分。 -/
def triangleComparison (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) :=
  squareFrameTriangleComparison (squareFrameComparison R d v) j

/-- 概要：元上下比較の二短辺制限は指定元側面を全単体で保持する。
方針：同じ元 prism の二側面回収式を使う。
規約：元四境界を保持。使われ方：全右面比較の指定境界照合。 -/
lemma triangleHomotopy_faces (j : Fin 2) :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫ (triangleHomotopy R d v j).h =
        (squareFrameTriangleFirst (squareFrameComparison R d v) j).h ∧
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 2})) ≫ (triangleHomotopy R d v j).h =
        (squareFrameTriangleLast (squareFrameComparison R d v) j).h :=
  squareFrameTriangleHomotopy_faces (squareFrameComparison R d v) j
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
