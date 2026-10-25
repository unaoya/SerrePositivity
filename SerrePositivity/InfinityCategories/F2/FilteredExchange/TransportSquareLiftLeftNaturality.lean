module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLiftEndpointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalEndpointPresentation
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionInitialEndpointIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoIdentity

/-!
概要：同じ底辺を固定した二四角形の左辺指定比較は、元の左上頂点像に自然。
方針：全延長の辺制限の正方形から、固定底辺内の始点像を消去する。
規約：元の指定比較を保持。使われ方：三辺比較の選択照合。
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
  {f : P ⟶ vertexFiber p a} (L M : TransportSquareLift p s f)

set_option maxHeartbeats 2000000 in
-- 元の指定比較の型に含まれる、交換した二端点表示の検証に必要。
/-- 元の左上頂点比較と左辺の指定比較の合成は、同じ元の直接左辺比較。 -/
lemma TransportSquareLift.leftComparison_naturality :
    L.topLeftIso M ≪≫ M.leftComparison = L.leftComparison := by
  let r := (Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const a := by
    rw [Category.assoc, s.inner_zero, intervalMappingUncurry_zero]
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const c := by
    rw [Category.assoc, s.inner_zero, intervalMappingUncurry_one]
  have hs : (prismEndpoint 0 P ≫ r) ≫ L.square = f ≫ vertexFiberι p a :=
    (Category.assoc _ _ _).trans L.left_start
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = f ≫ vertexFiberι p a :=
    (Category.assoc _ _ _).trans M.left_start
  have he : (prismEndpoint 1 P ≫ r) ≫ L.square = L.topLeft ≫ vertexFiberι p c :=
    (Category.assoc _ _ _).trans L.left_finish
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.topLeft ≫ vertexFiberι p c :=
    (Category.assoc _ _ _).trans M.left_finish
  exact relativeExtensionInterval_source_square_of_initial_at_endpoint p s.square
    (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) (diagonalUniversalPrism p f s.bottom)
    transportSquareBottom_base L.square M.square L.over_base M.over_base L.zero M.zero
    r a c ha hb f L.topLeft M.topLeft hs hs' he he' s.left s.inner_zero
    (prismEndpoint 0 P) rfl (prismEndpoint 0 P ≫ prismEndpoint 1 _) rfl
    transportSquareTopLeft_base
    (by rw [Category.assoc]; exact L.topLeft_ι.symm)
    (by rw [Category.assoc]; exact M.topLeft_ι.symm)

end SerrePositivity.InfinityCategories.F2
