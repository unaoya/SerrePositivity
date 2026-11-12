module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronFromComparisons

/-! # 八面体模型から任意の入力への輸送

概要：任意の合成可能な二射について Arrow として等しい八面体模型があれば八面体公理が成立する。
方針：Arrow の等号から三対象の等号同型と可換式を取り、Mathlib の同型輸送を使う。
規約：一般の前三角圏を扱う。使われ方：安定 ∞ 圏の IsTriangulated instance。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Pretriangulated Triangulated Limits
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：全ての合成可能な二射が Arrow として等しい八面体模型を持てば三角圏である。
方針：模型の第一・第二辺の等号から等号同型を作り、IsTriangulated.mk' に渡す。
規約：入力の distinguished 三角形の選択は Mathlib の一般の輸送で処理する。
使われ方：二長方形による幾何学的な八面体の全入力への適用。 -/
lemma isTriangulated_of_octahedronModels {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (h : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OctahedronModel (Arrow.mk f) (Arrow.mk g)) : IsTriangulated C := by
  apply IsTriangulated.mk'
  intro A₀ B₀ D₀ f₀ g₀
  obtain ⟨A, B, D, Z₁₂, Z₂₃, Z₁₃, f, g, v₁₂, w₁₂, v₂₃, w₂₃, v₁₃, w₁₃,
    H₁₂, H₂₃, H₁₃, hf, hg, H⟩ := h f₀ g₀
  obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  obtain ⟨hB', hD, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  refine ⟨A, B, D, Z₁₂, Z₂₃, Z₁₃, f, g, eqToIso hA.symm, eqToIso hB.symm,
    eqToIso hD.symm, ?_, ?_, v₁₂, w₁₂, H₁₂, v₂₃, w₂₃, H₂₃, v₁₃, w₁₃, H₁₃, H⟩
  · change f₀ ≫ eqToHom hB.symm = eqToHom hA.symm ≫ f
    rw [hf]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · change g₀ ≫ eqToHom hD.symm = eqToHom hB.symm ≫ g
    rw [hg]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
