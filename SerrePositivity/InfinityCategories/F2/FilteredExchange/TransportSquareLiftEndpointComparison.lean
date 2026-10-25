module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLiftComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionPrismEndpointWitness

/-!
概要：同じ底辺を固定する二実四角形の上二頂点を、元の全延長の指定比較で比較する。
方針：同じ底辺からの可縮な延長空間を、実際の二つの角で評価する。
規約：元の持ち上げと指定比較を保持。使われ方：三辺比較の中間因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
  {f : P ⟶ vertexFiber p a}

/-- 元の固定底辺は、元の全四角形の同じ底辺を被覆する。 -/
lemma transportSquareBottom_base : diagonalUniversalPrism p f s.bottom ≫ p =
    prismEndpoint 0 _ ≫ s.square :=
  (diagonalUniversalPrism_projection p f s.bottom).trans s.zero.symm

/-- 左上角の底は同じ元の左上頂点。 -/
lemma transportSquareTopLeft_base :
    (prismEndpoint 0 P ≫ prismEndpoint 1 _) ≫ s.square = SSet.const c := by
  rw [Category.assoc, s.one, intervalMappingUncurry_zero]

/-- 右上角の底は同じ元の右上頂点。 -/
lemma transportSquareTopRight_base :
    (prismEndpoint 1 P ≫ prismEndpoint 1 _) ≫ s.square = SSet.const d := by
  rw [Category.assoc, s.one, intervalMappingUncurry_one]

variable (L M : TransportSquareLift p s f)

/-- 二実四角形の左上頂点の元の指定比較。 -/
def TransportSquareLift.topLeftIso : FunctorIso L.topLeft M.topLeft :=
  relativeExtensionFiberEndpoint_witnessIso p s.square (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) (diagonalUniversalPrism p f s.bottom)
    transportSquareBottom_base (prismEndpoint 0 P ≫ prismEndpoint 1 _) c
    transportSquareTopLeft_base L.square M.square L.over_base M.over_base L.zero M.zero
    L.topLeft M.topLeft (by rw [Category.assoc]; exact L.topLeft_ι.symm)
    (by rw [Category.assoc]; exact M.topLeft_ι.symm)

/-- 二実四角形の右上頂点の元の指定比較。 -/
def TransportSquareLift.topRightIso : FunctorIso L.topRight M.topRight :=
  relativeExtensionFiberEndpoint_witnessIso p s.square (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) (diagonalUniversalPrism p f s.bottom)
    transportSquareBottom_base (prismEndpoint 1 P ≫ prismEndpoint 1 _) d
    transportSquareTopRight_base L.square M.square L.over_base M.over_base L.zero M.zero
    L.topRight M.topRight (by rw [Category.assoc]; exact L.topRight_ι.symm)
    (by rw [Category.assoc]; exact M.topRight_ι.symm)

/-- 同じ二実四角形の全延長比較を、同じ実辺へ制限した指定同型。 -/
def TransportSquareLift.restrictionIso (r : (Δ[1] : SSet.{u}) ⊗ P ⟶ Δ[1] ⊗ (Δ[1] ⊗ P)) :=
  relativeExtensionPrismRestrictionIso p s.square (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) (diagonalUniversalPrism p f s.bottom)
    transportSquareBottom_base L.square M.square L.over_base M.over_base L.zero M.zero r

end SerrePositivity.InfinityCategories.F2
