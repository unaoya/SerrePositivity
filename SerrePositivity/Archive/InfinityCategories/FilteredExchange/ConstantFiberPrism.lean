module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalRestrictedComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalSquareConstant

/-!
概要：元の定値区間の輸送比較に使う実定値 prism と、その同じ指定値を保持する。
方針：時間を忘れる射に元の始点族を合成し、両端と底を計算する。
規約：定値比較を選び直さない。使われ方：定値終辺の消去の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} (p : E ⟶ B) {a : B _⦋0⦌} (f : P ⟶ vertexFiber p a)

/-- 元の始点を時間方向で固定した、同じ実 prism。 -/
def constantFiberPrism : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  snd (Δ[1] : SSet.{u}) P ≫ f ≫ vertexFiberι p a

/-- 同じ実定値 prism のどちらの端点も、元の始点族。 -/
lemma constantFiberPrism_endpoint (i : Fin 2) :
    prismEndpoint i P ≫ constantFiberPrism p f = f ≫ vertexFiberι p a := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ実定値 prism の底は、元の固定頂点に定値。 -/
lemma constantFiberPrism_projection : constantFiberPrism p f ≫ p = SSet.const a := by
  rw [constantFiberPrism, Category.assoc, Category.assoc, vertexFiberι_comp,
    SSet.comp_const, SSet.comp_const]

/-- 元の実定値 prism の係数制限は、同じ元の始点の係数制限。 -/
lemma constantFiberPrism_precomp {Q : SSet.{u}} (q : Q ⟶ P) :
    ((Δ[1] : SSet.{u}) ◁ q) ≫ constantFiberPrism p f = constantFiberPrism p (q ≫ f) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の定値輸送比較は、同じ実定値 prism の元の区間比較の逆そのもの。 -/
lemma diagonalFiberTransport_constantIso_eq_prism [LeftFibration p]
    (c : P ⟶ intervalMappingSpace a a) (hc : intervalMappingUncurry c = SSet.const a) :
    diagonalFiberTransport_constantIso p f c hc =
      (leftFibrationPrism_transportIntervalIso p f f c (constantFiberPrism p f)
        (constantFiberPrism_endpoint p f 0) (constantFiberPrism_endpoint p f 1)
        ((constantFiberPrism_projection p f).trans hc.symm)).symm := rfl

end SerrePositivity.InfinityCategories.F2
