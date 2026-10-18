module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnit
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
概要：KST §3.1 の diagram-module 係数圏の結合律。
方針：包含がそろう場合は Hom の標準同定で係数遷移後の乗法の結合律へ戻す。
規約：包含のない場合は tensor の零性で処理する。
使われ方：全 diagram-module を表す dg 圏の組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]

/-- 概要：三つの包含がある場合の diagram-module 係数圏の結合律。
方針：包含の同定射で前合成し、四つの合成公式と代数図式の関手性を使う。
規約：KST §3.1。使われ方：結合律の非零の場合。 -/
theorem diagramModule_assoc_of_le (F : J ⥤ Mon (Complex R)) {i j k l : J}
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    (α_ (diagramModuleHom F i j) (diagramModuleHom F j k) (diagramModuleHom F k l)).inv ≫
      diagramModuleComp F i j k ▷ _ ≫ diagramModuleComp F i k l =
    _ ◁ diagramModuleComp F j k l ≫ diagramModuleComp F i j l := by
  have : IsIso (diagramModuleHomInclusion F hij) := by
    unfold diagramModuleHomInclusion
    infer_instance
  have : IsIso (diagramModuleHomInclusion F hjk) := by
    unfold diagramModuleHomInclusion
    infer_instance
  have : IsIso (diagramModuleHomInclusion F hkl) := by
    unfold diagramModuleHomInclusion
    infer_instance
  apply (cancel_epi (diagramModuleHomInclusion F hij ⊗ₘ
    (diagramModuleHomInclusion F hjk ⊗ₘ diagramModuleHomInclusion F hkl))).mp
  rw [associator_inv_naturality_assoc, tensorHom_comp_whiskerRight_assoc,
    diagramModuleComp_on_le]
  rw [← Category.assoc ((F.map (homOfLE hjk)).hom ⊗ₘ 𝟙 _) MonObj.mul
    (diagramModuleHomInclusion F (hij.trans hjk))]
  rw [← whiskerRight_comp_tensorHom_assoc
    (((F.map (homOfLE hjk)).hom ⊗ₘ 𝟙 _) ≫ MonObj.mul)
    (diagramModuleHomInclusion F (hij.trans hjk)) (diagramModuleHomInclusion F hkl),
    diagramModuleComp_on_le]
  rw [tensorHom_comp_whiskerLeft_assoc, diagramModuleComp_on_le]
  rw [← Category.assoc ((F.map (homOfLE hkl)).hom ⊗ₘ 𝟙 _) MonObj.mul
    (diagramModuleHomInclusion F (hjk.trans hkl))]
  rw [← whiskerLeft_comp_tensorHom_assoc (diagramModuleHomInclusion F hij)
    (((F.map (homOfLE hkl)).hom ⊗ₘ 𝟙 _) ≫ MonObj.mul)
    (diagramModuleHomInclusion F (hjk.trans hkl)), diagramModuleComp_on_le]
  rw [show F.map (homOfLE (hjk.trans hkl)) =
    F.map (homOfLE hjk) ≫ F.map (homOfLE hkl) from CategoryTheory.Functor.map_comp F _ _]
  have ha := diagramAlgebraMul_assoc (F.map (homOfLE hjk)) (F.map (homOfLE hkl))
  simpa only [diagramAlgebraMul, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun t => (α_ (F.obj j).X (F.obj k).X (F.obj l).X).inv ≫ t ≫
      diagramModuleHomInclusion F (hij.trans (hjk.trans hkl))) ha

/-- 概要：零複体を最初の因子に持つ tensor は零対象。
方針：恒等射を tensor 恒等射の式へ移し、零対象の恒等射の零性を使う。
規約：KST §3.1。使われ方：包含のない場合の結合律。 -/
theorem diagramComplexTensor_isZero_left {K : Complex R} (hK : IsZero K) (L : Complex R) :
    IsZero (K ⊗ L) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← id_tensorHom_id, hK.eq_of_src (𝟙 K) 0, MonoidalPreadditive.zero_tensor]

/-- 概要：零複体を第二因子に持つ tensor は零対象。
方針：恒等射の tensor 式と零射の tensor の零性を使う。
規約：KST §3.1。使われ方：包含のない場合の結合律。 -/
theorem diagramComplexTensor_isZero_right (K : Complex R) {L : Complex R} (hL : IsZero L) :
    IsZero (K ⊗ L) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← id_tensorHom_id, hL.eq_of_src (𝟙 L) 0, MonoidalPreadditive.tensor_zero]

/-- 概要：全ての対象についての diagram-module 係数圏の結合律。
方針：三つの包含があれば係数乗法の結合律、なければ元の三重 Hom の零性を使う。
規約：KST §3.1、Mathlib の dg 圏 constructor の associator を含む式。
使われ方：全 diagram-module を表す dg 圏の結合律フィールド。 -/
theorem diagramModule_assoc (F : J ⥤ Mon (Complex R)) (i j k l : J) :
    (α_ (diagramModuleHom F i j) (diagramModuleHom F j k) (diagramModuleHom F k l)).inv ≫
      diagramModuleComp F i j k ▷ _ ≫ diagramModuleComp F i k l =
    _ ◁ diagramModuleComp F j k l ≫ diagramModuleComp F i j l := by
  by_cases hij : i ≤ j
  · by_cases hjk : j ≤ k
    · by_cases hkl : k ≤ l
      · exact diagramModule_assoc_of_le F hij hjk hkl
      · exact (diagramComplexTensor_isZero_right _
          (diagramComplexTensor_isZero_right _ (diagramModuleHom_isZero F hkl))).eq_of_src _ _
    · exact (diagramComplexTensor_isZero_right _
        (diagramComplexTensor_isZero_left (diagramModuleHom_isZero F hjk) _)).eq_of_src _ _
  · exact (diagramComplexTensor_isZero_left (diagramModuleHom_isZero F hij) _).eq_of_src _ _

end SerrePositivity.KST.DerivedBlowup
