module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceBoundaryImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoWhiskerCancellation

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
variable {A A₀ X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x))
  (k : A₀ ⟶ A)
/-- 概要：同じ元の境界比較の旧族への制限は、旧族で構成した指定比較そのもの。
方針：元の全比較と前合成の合成則。規約：指定値を保持。使われ方：元の指定変換の保持。 -/
lemma coneTerminalSliceBoundaryFunctorIso_precomp : HEq
    ((coneTerminalSliceBoundaryFunctorIso x b hb W hp ht).precomp k)
    (coneTerminalSliceBoundaryFunctorIso x (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp])
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact ht)) := by
  let J := joinMap k (𝟙 (Δ[0] : SSet.{u}))
  have hb₀ : joinInr A₀ (Δ[0] : SSet.{u}) ≫ (J ≫ b) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact hb
  have hp₀ : (J ≫ W) ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = J ≫ b := by
    rw [Category.assoc, hp]
  have ht₀ : joinInr A₀ (Δ[0] : SSet.{u}) ≫ (J ≫ W) =
      SSet.yonedaEquiv.symm (sliceIdentityCone x) := by
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact ht
  let e := coneTerminalSliceFunctorIso x b hb W hp ht
  let e₀ := coneTerminalSliceFunctorIso x (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  let d := coneTerminalSliceBoundaryFunctorIso x b hb W hp ht
  let d₀ := coneTerminalSliceBoundaryFunctorIso x (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  have hd : HEq d (e.precomp (joinInl A Δ[0])) :=
    coneTerminalSliceBoundaryFunctorIso_heq_precomp x b hb W hp ht
  have hd₀ : HEq d₀ (e₀.precomp (joinInl A₀ Δ[0])) :=
    coneTerminalSliceBoundaryFunctorIso_heq_precomp x (J ≫ b) hb₀ (J ≫ W) hp₀ ht₀
  have h0 := F2.functorIso_precomp_heq_of_heq (e.precomp (joinInl A Δ[0])) d
    rfl (coneTerminalSliceLift_old x b hb) hd k
  have h1 := F2.functorIso_precomp_precomp e (joinInl A Δ[0]) k
  have h2 := F2.functorIso_precomp_heq_of_map_eq e
    (joinInl_joinMap k (𝟙 (Δ[0] : SSet.{u}))).symm
  have h3 := F2.functorIso_precomp_precomp e J (joinInl A₀ Δ[0])
  have hnat : HEq (e.precomp J) e₀ := coneTerminalSliceFunctorIso_precomp x b hb W hp ht k
  have h4 := F2.functorIso_precomp_heq_of_heq e₀ (e.precomp J)
    rfl (coneTerminalSliceLift_precomp x b hb k).symm hnat (joinInl A₀ Δ[0])
  exact h0.trans ((heq_of_eq h1).trans (h2.trans ((heq_of_eq h3.symm).trans
    (h4.trans hd₀.symm))))
end SerrePositivity.InfinityCategories.F2.Ind
