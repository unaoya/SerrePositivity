module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceBoundaryImage
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：同じ底と終点を固定した始域境界の全族の比較は、旧族で同じ指定比較に制限される。
方針：全余錐の比較の自然性と、元の始域境界の比較の回収を合成する。
規約：型の等号による表示変更まで指定同型の値を保持し、別の比較を選ばない。
使われ方：極大点評価の指定変換を元の同じ旧族で保持する相対余錐。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A A₀ X : SSet.{u}} [Quasicategory X] (p : (Δ[0] : SSet.{u}) ⟶ X)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = p)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (p))
  (hp : W ≫ sliceOverProjection (p) = b)
  (ht : sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const (SSet.yonedaEquiv p))
  (k : A₀ ⟶ A)
/-- 概要：同じ元の境界比較の旧族への制限は、旧族で構成した指定比較そのもの。
方針：元の全比較と前合成の合成則。規約：指定値を保持。使われ方：元の指定変換の保持。 -/
lemma conePointSliceBoundaryFunctorIso_precomp : HEq
    ((conePointSliceBoundaryFunctorIso p b hb W hp ht).precomp k)
    (conePointSliceBoundaryFunctorIso p (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp])
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact ht)) := by
  let J := joinMap k (𝟙 (Δ[0] : SSet.{u}))
  have hb₀ : joinInr A₀ (Δ[0] : SSet.{u}) ≫ (J ≫ b) = p := by
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact hb
  have hp₀ : (J ≫ W) ≫ sliceOverProjection (p) = J ≫ b := by
    rw [Category.assoc, hp]
  have ht₀ : sliceOverUncurry (joinInr A₀ (Δ[0] : SSet.{u}) ≫ (J ≫ W)) =
      SSet.const (SSet.yonedaEquiv p) := by
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact ht
  let e := conePointSliceFunctorIso p b hb W hp ht
  let e₀ := conePointSliceFunctorIso p (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  let d := conePointSliceBoundaryFunctorIso p b hb W hp ht
  let d₀ := conePointSliceBoundaryFunctorIso p (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  have hd : HEq d (e.precomp (joinInl A Δ[0])) :=
    conePointSliceBoundaryFunctorIso_heq_precomp p b hb W hp ht
  have hd₀ : HEq d₀ (e₀.precomp (joinInl A₀ Δ[0])) :=
    conePointSliceBoundaryFunctorIso_heq_precomp p (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  have h0 := F2.functorIso_precomp_heq_of_heq (e.precomp (joinInl A Δ[0])) d
    rfl (conePointSliceLift_old p b hb) hd k
  have h1 := F2.functorIso_precomp_precomp e (joinInl A Δ[0]) k
  have h2 := F2.functorIso_precomp_heq_of_map_eq e
    (joinInl_joinMap k (𝟙 (Δ[0] : SSet.{u}))).symm
  have h3 := F2.functorIso_precomp_precomp e J (joinInl A₀ Δ[0])
  have hnat : HEq (e.precomp J) e₀ := conePointSliceFunctorIso_precomp p b hb W hp ht k
  have h4 := F2.functorIso_precomp_heq_of_heq e₀ (e.precomp J)
    rfl (conePointSliceLift_precomp p b hb k).symm hnat (joinInl A₀ Δ[0])
  exact h0.trans ((heq_of_eq h1).trans (h2.trans ((heq_of_eq h3.symm).trans
    (h4.trans hd₀.symm))))
end SerrePositivity.InfinityCategories.F2.Ind
