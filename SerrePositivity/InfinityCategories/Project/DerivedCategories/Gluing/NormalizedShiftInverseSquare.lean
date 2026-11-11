module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizedShiftInverseImage
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 正規化した逆斉次元による augmentation の厳密正方形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (F : DGFunctor R (RightModule R D) (RightModule R C))
  (U : RightModule R D) (V : RightModule R C) (n : ℤ)
  (a : ForgetEnrichment.of (Complex R) V ⟶ ForgetEnrichment.of (Complex R) (F.obj U))

/-- 逆元も、同じ augmentation と正規化シフト同型の厳密正方形を満たす。 -/
lemma dgGluingNormalizedShiftInverseSquare :
    (eHomWhiskerRight (Complex R) a
      (ForgetEnrichment.of (Complex R) (F.obj (shiftModule n U)))).f (-n)
        ((F.map U (shiftModule n U)).f (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R D n U)) =
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) V)
      (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)).f (-n)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R C n V) := by
  apply moduleHomElement_ext R C
  intro c
  have hl := moduleHomWhiskerRight_apply_π R C
    (M := ForgetEnrichment.of (Complex R) V)
    (N := ForgetEnrichment.of (Complex R) (F.obj U))
    (P := ForgetEnrichment.of (Complex R) (F.obj (shiftModule n U))) a (-n)
    ((F.map U (shiftModule n U)).f (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R D n U)) c
  have hr := moduleHomWhiskerLeft_apply_π R C
    (T := ForgetEnrichment.of (Complex R) V)
    (M := ForgetEnrichment.of (Complex R) (shiftModule n V))
    (N := ForgetEnrichment.of (Complex R) (F.obj (shiftModule n U)))
    (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)
    (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R C n V) c
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply Cochain.ext
  intro i j hij
  have hji : i = j + n := by omega
  subst i
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v]
  change ((moduleEvaluation R C c).map a).f (j + n) ≫
    (((moduleHomπ R C (F.obj U) (F.obj (shiftModule n U)) c).f (-n)
      ((F.map U (shiftModule n U)).f (-n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R D n U))).v
        (j + n) j (by omega)) =
    (((moduleHomπ R C V (shiftModule n V) c).f (-n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn R C n V)).v (j + n) j (by omega)) ≫
    ((moduleEvaluation R C c).map
      (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)).f j
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftInImage_v, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftIn_v,
    Category.id_comp, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    moduleShiftMap_eval]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
