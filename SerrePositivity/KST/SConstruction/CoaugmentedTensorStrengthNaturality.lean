module
public import SerrePositivity.KST.SConstruction.CoaugmentedTensorStrength

/-! # 元の商射と全作用を保つ tensor strength の自然性
概要：全パラメータ作用の商射との整合性を、同じ strength による像へ移す。
方針：乗法比較の自然性と三重 tensor の全単体結合則を使う。
規約：商の逆は仮定しない。使われ方：smash と suspension 比較の全族自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F)

/-- 左 strength は、写した右変数の元の射と厳密に可換する。 -/
lemma coaugmentedTensorLeftStrength_naturality {K X Y : SSet.{u}} (f : X ⟶ Y) :
    (K ◁ F.map f) ≫ coaugmentedTensorLeftStrength F η K Y =
      coaugmentedTensorLeftStrength F η K X ≫ F.map (K ◁ f) := by
  ext n t
  exact types_congr_hom (NatTrans.congr_app (μ_natural_right F K f) n)
    ((η.app K).app n t.1, t.2)

/-- 右 strength は、写した左変数の元の射と厳密に可換する。 -/
lemma coaugmentedTensorRightStrength_naturality {X Y P : SSet.{u}} (f : X ⟶ Y) :
    (F.map f ▷ P) ≫ coaugmentedTensorRightStrength F η Y P =
      coaugmentedTensorRightStrength F η X P ≫ F.map (f ▷ P) := by
  ext n t
  exact types_congr_hom (NatTrans.congr_app (μ_natural_left F f P) n)
    (t.1, (η.app P).app n t.2)

/-- 元の商射上で可換な全パラメータ作用は、同じ strength の像でも厳密に可換する。 -/
lemma coaugmentedTensorStrength_quotient_action {K X Y P Q R : SSet.{u}}
    (a : X ⊗ P ⟶ Y) (b : Q ⊗ P ⟶ R) (j : K ⊗ X ⟶ Q) (k : K ⊗ Y ⟶ R)
    (h : (j ▷ P) ≫ b = (α_ K X P).hom ≫ (K ◁ a) ≫ k) :
    ((coaugmentedTensorLeftStrength F η K X ≫ F.map j) ▷ P) ≫
      coaugmentedTensorRightStrength F η Q P ≫ F.map b =
    (α_ K (F.obj X) P).hom ≫
      (K ◁ (coaugmentedTensorRightStrength F η X P ≫ F.map a)) ≫
      coaugmentedTensorLeftStrength F η K Y ≫ F.map k := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← Category.assoc (F.map j ▷ P), coaugmentedTensorRightStrength_naturality]
  simp only [Category.assoc, ← F.map_comp]
  rw [h]
  have hc := congrArg (fun q => q ≫ F.map k)
    (coaugmentedTensorStrength_action F η (K := K) a)
  simpa only [F.map_comp, Category.assoc] using hc.symm

end SerrePositivity.KST.SConstruction
