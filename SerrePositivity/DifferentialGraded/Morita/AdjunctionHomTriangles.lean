module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelGeneratorHom

/-! # 右随伴のHom比較を三角形に沿って拡張する

## 概要
指定射L(R)→YによるHom比較の全単射性を、三角形の両端から中央へ運ぶ。

## 方針
二つのYoneda完全列を追い、全射性には逆回転、単射性にはshiftした第一頂点を用いる。

## 規約と注意
随伴の存在は仮定しない。指定した実際の三角関手と標的射だけを使う。

## 使われ方
U16aのtelescopeの生成元上のHom全単射を全入力へ拡張する局所化帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)

/-- 指定射L(R)→Yから定まる入力XでのHom比較。 -/
abbrev brownHomComparison (X : DerivedModuleCategory A D) (f : X ⟶ R) := L.map f ≫ r

/-- Hom比較の単射性から、そのkernelは零。 -/
lemma brownHomComparison_kernel_zero {X : DerivedModuleCategory A D}
    (hX : Function.Injective (brownHomComparison A D E L r X))
    (f : X ⟶ R) (hf : brownHomComparison A D E L r X f = 0) : f = 0 := by
  apply hX
  simpa only [brownHomComparison, L.map_zero, zero_comp] using hf

/-- 両端と必要なshiftでのHom全単射から、三角形中央のHom全単射を得る。 -/
lemma brownHomComparison_triangle (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h1 : Function.Bijective (brownHomComparison A D E L r T.obj₁))
    (h3 : Function.Bijective (brownHomComparison A D E L r T.obj₃))
    (h1s : Function.Surjective (brownHomComparison A D E L r (T.obj₁⟦(1 : ℤ)⟧)))
    (h3s : Function.Injective (brownHomComparison A D E L r T.invRotate.obj₁)) :
    Function.Bijective (brownHomComparison A D E L r T.obj₂) := by
  have hk (f : T.obj₂ ⟶ R) (hf : L.map f ≫ r = 0) : f = 0 := by
    have haf : T.mor₁ ≫ f = 0 := by
      apply brownHomComparison_kernel_zero A D E L r h1.1
      simp only [brownHomComparison, L.map_comp, Category.assoc, hf, comp_zero]
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f haf
    have hbg : L.map T.mor₂ ≫ (L.map g ≫ r) = 0 := by
      rw [← Category.assoc, ← L.map_comp, ← hg, hf]
    obtain ⟨k, hk⟩ := (L.mapTriangle.obj T).yoneda_exact₃ (L.map_distinguished T hT)
      (L.map g ≫ r) hbg
    obtain ⟨a, ha⟩ := h1s ((L.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ k)
    change L.map a ≫ r = (L.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ k at ha
    have hga : g = T.mor₃ ≫ a := by
      apply h3.1
      change L.map g ≫ r = L.map (T.mor₃ ≫ a) ≫ r
      rw [L.map_comp, Category.assoc, ha]
      change L.map g ≫ r = (L.map T.mor₃ ≫
        (L.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ k at hk
      simpa only [Category.assoc] using hk
    rw [hg, hga, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  constructor
  · intro f g h
    apply sub_eq_zero.mp
    apply hk (f-g)
    change L.map f ≫ r = L.map g ≫ r at h
    rw [L.map_sub, sub_comp, h, sub_self]
  · intro f
    obtain ⟨a, ha⟩ := h1.2 (L.map T.mor₁ ≫ f)
    change L.map a ≫ r = L.map T.mor₁ ≫ f at ha
    have hza : T.invRotate.mor₁ ≫ a = 0 := by
      apply brownHomComparison_kernel_zero A D E L r h3s
      change L.map (T.invRotate.mor₁ ≫ a) ≫ r = 0
      have hz := comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang T hT)
      change T.invRotate.mor₁ ≫ T.mor₁ = 0 at hz
      erw [L.map_comp, Category.assoc, ha, ← Category.assoc, ← L.map_comp, hz,
        L.map_zero, zero_comp]
    obtain ⟨b, hb⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a hza
    change T.obj₂ ⟶ R at b
    change a = T.mor₁ ≫ b at hb
    have hdiff : L.map T.mor₁ ≫ (f - L.map b ≫ r) = 0 := by
      rw [comp_sub, ← Category.assoc, ← L.map_comp, ← hb, ← ha, sub_self]
    obtain ⟨c, hc⟩ := (L.mapTriangle.obj T).yoneda_exact₂ (L.map_distinguished T hT)
      (f - L.map b ≫ r) hdiff
    obtain ⟨d, hd⟩ := h3.2 c
    change L.map d ≫ r = c at hd
    refine ⟨b + T.mor₂ ≫ d, ?_⟩
    change L.map (b + T.mor₂ ≫ d) ≫ r = f
    rw [L.map_add, add_comp, L.map_comp, Category.assoc, hd]
    change f - L.map b ≫ r = L.map T.mor₂ ≫ c at hc
    rw [← hc]
    exact add_sub_cancel _ _

end SerrePositivity.DifferentialGraded.Morita
