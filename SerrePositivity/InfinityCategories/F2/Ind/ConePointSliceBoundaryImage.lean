module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceFunctorIsoNaturality

/-!
概要：任意の元の点の境界比較は、同じ全余錐比較を始域で制限した指定値そのもの。
方針：元の境界表示の型移送と、相対関手空間の包含の自然性を照合する。
規約：元の点写像と比較同型の指定値を保持する。
使われ方：元の極大点評価の指定変換を旧族で保持する相対余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：型の等号移送は元の値を保持。方針：等号を消去。
規約：元の指定値。使われ方：元の境界比較の型の表示変更を戻す。 -/
private theorem point_eq_mp_heq {α β : Sort u} (h : α = β) (a : α) : HEq (h.mp a) a := by
  cases h
  rfl
variable {A X : SSet.{u}} [Quasicategory X] (p : (Δ[0] : SSet.{u}) ⟶ X)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver p) (hp : W ≫ sliceOverProjection p = b)
  (ht : sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const (SSet.yonedaEquiv p))
/-- 概要：元の始域境界の指定比較は、同じ全余錐の比較の元の制限。
方針：元の型の等号移送を戻す。規約：同じ指定値。使われ方：旧族での比較回収。 -/
lemma conePointSliceBoundaryRelativeIso_heq_map :
    HEq (conePointSliceBoundaryRelativeIso p b hb W hp ht)
      (VertexIso.map (conePointSliceRelativeIso p b hb W hp ht)
        (relativeFunctorPre (sliceOverProjection p) b (joinInl A (Δ[0] : SSet.{u})))) := by
  unfold conePointSliceBoundaryRelativeIso
  exact point_eq_mp_heq _ _
/-- 概要：元の点と全底を固定した境界比較を、元の全族の同じ同型で読む。
方針：元の相対関手空間の包含。規約：同じ指定値。使われ方：元の指定変換の保持。 -/
def conePointSliceBoundaryFunctorIso :
    FunctorIso (joinInl A (Δ[0] : SSet.{u}) ≫ W) (sliceOverCurry b hb) :=
  relativeFunctorVertexIsoImage _ _ _ _ _ _ (conePointSliceBoundaryRelativeIso p b hb W hp ht)
/-- 概要：元の全境界比較は、同じ全余錐比較の始域制限と指定値まで一致する。
方針：元の境界と包含の自然性。規約：同じ指定値。使われ方：旧族での比較回収。 -/
lemma conePointSliceBoundaryFunctorIso_heq_precomp : HEq
    (conePointSliceBoundaryFunctorIso p b hb W hp ht)
    ((conePointSliceFunctorIso p b hb W hp ht).precomp (joinInl A (Δ[0] : SSet.{u}))) := by
  dsimp only [conePointSliceBoundaryFunctorIso, conePointSliceFunctorIso]
  rw [relativeFunctorVertexIsoImage_precomp]
  apply relativeFunctorVertexIsoImage_heq
  · rfl
  · exact (conePointSliceLift_old p b hb).symm
  · exact conePointSliceBoundaryRelativeIso_heq_map p b hb W hp ht
/-- 概要：元の全底と持ち上げを等号で表示変更しても、同じ指定比較の値を保持する。
方針：元の両全射の等号を消去。規約：同じ指定値。使われ方：旧族での比較回収。 -/
lemma conePointSliceBoundaryFunctorIso_heq {b' : join A (Δ[0] : SSet.{u}) ⟶ X}
    (hb' : joinInr A Δ[0] ≫ b' = p) {W' : join A (Δ[0] : SSet.{u}) ⟶ sliceOver p}
    (hp' : W' ≫ sliceOverProjection p = b')
    (ht' : sliceOverUncurry (joinInr A Δ[0] ≫ W') = SSet.const (SSet.yonedaEquiv p))
    (hbb : b = b') (hWW : W = W') :
    HEq (conePointSliceBoundaryFunctorIso p b hb W hp ht)
      (conePointSliceBoundaryFunctorIso p b' hb' W' hp' ht') := by
  cases hbb
  cases hWW
  rfl
end SerrePositivity.InfinityCategories.F2.Ind
