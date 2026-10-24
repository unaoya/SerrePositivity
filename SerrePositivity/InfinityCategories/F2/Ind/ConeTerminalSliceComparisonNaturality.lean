module

public import SerrePositivity.InfinityCategories.F2.Ind.RightAnodyneRelativeLiftNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceLiftNaturality

/-!
概要：同じ終点への全余錐の相対比較は、元の試験形状の制限でも同じ指定比較を回収する。
方針：right-anodyne 相対比較の自然性と、標準持ち上げの厳密な全自然性を合成する。
規約：元の底と終点を固定し、同型の存在だけでなく指定値そのものを保持する。
使われ方：指定された極大点評価下の変換を、同じ旧族で保持する相対余錐の構成。
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
/-- 概要：同じ底と終点を固定した全余錐の比較は、旧族で元の同じ比較に制限される。
方針：同じ充満忠実な逆像を照合。規約：指定値を保持。使われ方：元の指定変換の保持。 -/
lemma coneTerminalSliceRelativeIso_precomp : HEq
    (VertexIso.map (coneTerminalSliceRelativeIso x b hb W hp ht)
      (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm x)) b (joinMap k (𝟙 Δ[0]))))
    (coneTerminalSliceRelativeIso x (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp])
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact ht)) := by
  have hn := rightAnodyneRelativeLiftIso_precomp
    (p := sliceOverProjection (SSet.yonedaEquiv.symm x)) (b := b)
    (f := W) (g := coneTerminalSliceLift x b hb) (hf := hp)
    (hg := coneTerminalSliceLift_projection x b hb)
    (j := joinMap k (𝟙 Δ[0])) (i₀ := joinInr A₀ (Δ[0] : SSet.{u}))
    (hi₀ := coneTip_rightAnodyne A₀)
    (hij := by rw [joinInr_joinMap, Category.id_comp]; exact coneTip_rightAnodyne A)
    (hh := by
      rw [joinInr_joinMap, Category.id_comp]
      exact ht.trans (coneTerminalSliceLift_tip x b hb).symm)
  have h := heq_of_eq hn
  simp only [joinInr_joinMap, Category.id_comp, coneTerminalSliceRelativeIso] at h ⊢
  refine h.trans ?_
  apply rightAnodyneRelativeLiftIso_heq
  · rfl
  · exact coneTerminalSliceLift_precomp x b hb k
end SerrePositivity.InfinityCategories.F2.Ind
