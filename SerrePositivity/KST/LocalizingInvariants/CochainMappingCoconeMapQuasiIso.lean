module

public import SerrePositivity.KST.LocalizingInvariants.CochainCoconeShiftCoordinates
public import SerrePositivity.KST.LocalizingInvariants.CochainConeMapQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionHomExt
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
概要：可換正方形の両側が準同型なら、元の mapping cocone 射も準同型である。
方針：実二座標で元の cone 射の shift と一致させ、cone の準同型性を移す。
規約：比較 cochain を保つ同じ射を使う。使われ方：cell 分解上の pullback 模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K₁ L₁ K₂ L₂ : Complex R}
  (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (h : d₁ ≫ b = a ≫ d₂)

lemma cochainMappingCoconeMap_eq_shift : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b h =
    (mappingCone.map d₁ d₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext d₂ p
  · calc
      _ = (mappingCocone.fst d₁).f p ≫ a.f p :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f _ _ _ _ _ _
      _ = (mappingCone.fst d₁).val.v (p - 1) p (by omega) ≫ a.f p := by
        rw [cochainCocone_fst_f]
      _ = (mappingCone.map d₁ d₂ a b h).f (p - 1) ≫
          (mappingCone.fst d₂).val.v (p - 1) p (by omega) :=
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneMap_f_fst_v _ _ _ _ _ _ _ (by omega)).symm
      _ = _ := by rw [cochainCocone_fst_f]; rfl
  · calc
      _ = (mappingCocone.snd d₁).v p (p - 1) (by omega) ≫ b.f (p - 1) :=
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v _ _ _ _ _ _ _ _
      _ = (mappingCone.snd d₁).v (p - 1) (p - 1) (add_zero _) ≫ b.f (p - 1) := by
        rw [cochainCocone_snd_v]
      _ = (mappingCone.map d₁ d₂ a b h).f (p - 1) ≫
          (mappingCone.snd d₂).v (p - 1) (p - 1) (add_zero _) :=
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneMap_f_snd_v _ _ _ _ _ _).symm
      _ = _ := by rw [cochainCocone_snd_v]; rfl

lemma cochainMappingCoconeMap_quasiIso (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b h) := by
  have := cochainConeMap_quasiIso d₁ d₂ a b h ha hb
  rw [cochainMappingCoconeMap_eq_shift]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants
