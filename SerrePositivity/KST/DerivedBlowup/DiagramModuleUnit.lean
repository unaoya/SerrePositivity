module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleHom
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraMultiplication

/-!
概要：KST §3.1 の diagram-module 係数圏の左右の単位律。
方針：包含がなければ零 Hom の一意性、包含があれば係数遷移後の乗法の単位律を使う。
規約：Mathlib の dg 圏 constructor の unitor を含む形で述べる。
使われ方：全 diagram-module を表す dg 圏の組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open DifferentialGraded
open scoped ZeroObject

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]

/-- 概要：包含が存在しないとき diagram-module の Hom は零対象。
方針：条件分岐を解消して零複体の性質を使う。
規約：KST §3.1。使われ方：包含のない場合の圏法則。 -/
theorem diagramModuleHom_isZero (F : J ⥤ Mon (Complex R)) {i j : J} (h : ¬i ≤ j) :
    IsZero (diagramModuleHom F i j) := by
  rw [diagramModuleHom, ite_eq_right h]
  exact isZero_zero _

/-- 概要：diagram-module 係数圏の左単位律。
方針：包含に沿って係数遷移の単位保存を使い、包含がなければ零 Hom の一意性を使う。
規約：KST §3.1。使われ方：dg 圏の左単位の構造フィールド。 -/
theorem diagramModule_left_unit (F : J ⥤ Mon (Complex R)) (i j : J) :
    (λ_ (diagramModuleHom F i j)).inv ≫ diagramModuleId F i ▷ _ ≫
      diagramModuleComp F i i j = 𝟙 _ := by
  by_cases hij : i ≤ j
  · have : IsIso (diagramModuleHomInclusion F hij) := by
      unfold diagramModuleHomInclusion
      infer_instance
    apply (cancel_epi (diagramModuleHomInclusion F hij)).mp
    rw [leftUnitor_inv_naturality_assoc]
    simp only [diagramModuleId, comp_whiskerRight, Category.assoc, Category.comp_id]
    rw [whisker_exchange_assoc, ← tensorHom_def'_assoc, diagramModuleComp_on_le]
    change (λ_ (F.obj j).X).inv ≫ MonObj.one ▷ (F.obj j).X ≫
      diagramAlgebraMul (F.map (homOfLE hij)) ≫ diagramModuleHomInclusion F hij =
        diagramModuleHomInclusion F hij
    rw [diagramAlgebraMul_one_assoc, Iso.inv_hom_id_assoc]
  · exact (diagramModuleHom_isZero F hij).eq_of_src _ _

/-- 概要：diagram-module 係数圏の右単位律。
方針：恒等包含に対応する環射を簡約し、目標代数の右単位律を使う。
規約：KST §3.1。使われ方：dg 圏の右単位の構造フィールド。 -/
theorem diagramModule_right_unit (F : J ⥤ Mon (Complex R)) (i j : J) :
    (ρ_ (diagramModuleHom F i j)).inv ≫ _ ◁ diagramModuleId F j ≫
      diagramModuleComp F i j j = 𝟙 _ := by
  by_cases hij : i ≤ j
  · have : IsIso (diagramModuleHomInclusion F hij) := by
      unfold diagramModuleHomInclusion
      infer_instance
    apply (cancel_epi (diagramModuleHomInclusion F hij)).mp
    rw [rightUnitor_inv_naturality_assoc]
    simp only [diagramModuleId, whiskerLeft_comp, Category.assoc, Category.comp_id]
    rw [← whisker_exchange_assoc, ← tensorHom_def_assoc, diagramModuleComp_on_le]
    change (ρ_ (F.obj j).X).inv ≫ (F.obj j).X ◁ MonObj.one ≫
      diagramAlgebraMul (F.map (𝟙 j)) ≫ diagramModuleHomInclusion F hij =
        diagramModuleHomInclusion F hij
    rw [CategoryTheory.Functor.map_id, diagramAlgebraMul_id,
      MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]
  · exact (diagramModuleHom_isZero F hij).eq_of_src _ _

end SerrePositivity.KST.DerivedBlowup
