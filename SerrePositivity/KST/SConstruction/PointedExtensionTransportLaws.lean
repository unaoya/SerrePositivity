module
public import SerrePositivity.KST.SConstruction.PointedExtensionTransport

/-! # 延長空間の移送の関手法則
概要：延長の全パラメーター空間への移送は恒等・合成を厳密に保つ。
方針：写像空間への射影と一点への射影で等号を検証する。
規約：各次数のホモトピー類の等号には弱めない。
使われ方：入力の射列に沿う高次の Kan 延長の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping

/-- 恒等正方形による延長空間の移送は恒等射。 -/
lemma pointedExtensionTransport_id {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (h : A ⟶ Z) :
    pointedExtensionTransport i h i h (𝟙 A) (𝟙 B) (𝟙 Z)
      (by simp) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pointedExtensionTransport_projection, pointedMappingTransport_id,
      Category.comp_id, Category.id_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 二つの正方形による移送の合成は、合成正方形による移送と一致する。 -/
lemma pointedExtensionTransport_comp
    {A B Z A' B' Z' A'' B'' Z'' : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (h : A ⟶ Z) (i' : A' ⟶ B') (h' : A' ⟶ Z')
    (i'' : A'' ⟶ B'') (h'' : A'' ⟶ Z'')
    (a : A' ⟶ A) (b : B' ⟶ B) (z : Z ⟶ Z')
    (a' : A'' ⟶ A') (b' : B'' ⟶ B') (z' : Z' ⟶ Z'')
    (hi : a ≫ i = i' ≫ b) (hh : a ≫ h ≫ z = h')
    (hi' : a' ≫ i' = i'' ≫ b') (hh' : a' ≫ h' ≫ z' = h'')
    (hi'' : (a' ≫ a) ≫ i = i'' ≫ (b' ≫ b))
    (hh'' : (a' ≫ a) ≫ h ≫ (z ≫ z') = h'') :
    pointedExtensionTransport i h i' h' a b z hi hh ≫
      pointedExtensionTransport i' h' i'' h'' a' b' z' hi' hh' =
    pointedExtensionTransport i h i'' h'' (a' ≫ a) (b' ≫ b) (z ≫ z') hi'' hh'' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointedExtensionTransport_projection,
      ← Category.assoc, pointedExtensionTransport_projection, Category.assoc,
      pointedMappingTransport_comp, pointedExtensionTransport_projection]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.SConstruction
