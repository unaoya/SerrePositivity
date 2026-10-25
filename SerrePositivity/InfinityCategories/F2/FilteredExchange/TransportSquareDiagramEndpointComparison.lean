module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramComparison

/-!
概要：左下角だけを固定した二実四角形の、残る三頂点の元の指定比較。
方針：左下角の包含の左 anodyne 性と、同じ全延長の fiber 終点評価を使う。
規約：底辺の持ち上げは固定しない。使われ方：高次図式の任意の実面の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}

/-- 左下角から全四角形への包含は左 anodyne。 -/
lemma transportSquareOrigin_leftAnodyne (P : SSet.{u}) :
    leftAnodyneExtensions (prismEndpoint 0 P ≫ prismEndpoint 0 (Δ[1] ⊗ P)) :=
  leftAnodyneExtensions.comp_mem _ _
    (prismEndpoint_zero_leftAnodyne P) (prismEndpoint_zero_leftAnodyne _)

/-- 左下角の実値は、元の全四角形の左下角を被覆する。 -/
lemma transportSquareOrigin_base : (f ≫ vertexFiberι p a) ≫ p =
    (prismEndpoint 0 P ≫ prismEndpoint 0 _) ≫ s.square := by
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, Category.assoc, s.zero,
    intervalMappingUncurry_zero]

/-- 元の右下角の底。 -/
lemma transportSquareBottomRight_base :
    (prismEndpoint 1 P ≫ prismEndpoint 0 _) ≫ s.square = SSet.const b := by
  rw [Category.assoc, s.zero, intervalMappingUncurry_one]

variable [LeftFibration p] (D M : TransportSquareDiagram p s f)

/-- 左下角だけを固定する全延長比較の、元の右下頂点像。 -/
def TransportSquareDiagram.bottomRightIso : FunctorIso D.bottomRight M.bottomRight :=
  relativeExtensionFiberEndpoint_witnessIso p s.square (prismEndpoint 0 P ≫ prismEndpoint 0 _)
    (transportSquareOrigin_leftAnodyne P) (f ≫ vertexFiberι p a) transportSquareOrigin_base
    (prismEndpoint 1 P ≫ prismEndpoint 0 _) b transportSquareBottomRight_base
    D.square M.square D.over_base M.over_base D.origin M.origin D.bottomRight M.bottomRight
    D.bottomRight_eq M.bottomRight_eq

/-- 左下角だけを固定する全延長比較の、元の左上頂点像。 -/
def TransportSquareDiagram.topLeftIso : FunctorIso D.topLeft M.topLeft :=
  relativeExtensionFiberEndpoint_witnessIso p s.square (prismEndpoint 0 P ≫ prismEndpoint 0 _)
    (transportSquareOrigin_leftAnodyne P) (f ≫ vertexFiberι p a) transportSquareOrigin_base
    (prismEndpoint 0 P ≫ prismEndpoint 1 _) c transportSquareTopLeft_base
    D.square M.square D.over_base M.over_base D.origin M.origin D.topLeft M.topLeft
    D.topLeft_eq M.topLeft_eq

/-- 左下角だけを固定する全延長比較の、元の右上頂点像。 -/
def TransportSquareDiagram.topRightIso : FunctorIso D.topRight M.topRight :=
  relativeExtensionFiberEndpoint_witnessIso p s.square (prismEndpoint 0 P ≫ prismEndpoint 0 _)
    (transportSquareOrigin_leftAnodyne P) (f ≫ vertexFiberι p a) transportSquareOrigin_base
    (prismEndpoint 1 P ≫ prismEndpoint 1 _) d transportSquareTopRight_base
    D.square M.square D.over_base M.over_base D.origin M.origin D.topRight M.topRight
    D.topRight_eq M.topRight_eq

end SerrePositivity.InfinityCategories.F2
