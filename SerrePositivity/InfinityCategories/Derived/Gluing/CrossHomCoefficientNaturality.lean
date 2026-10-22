module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomFunctorMapElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficientPostAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficientModuleMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleFunctorNaturality

/-! C 因子上の同じ係数加群射は、D 因子の全 Hom 複体に関して自然。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "A" => DGGluingCFactor R C D M
local notation "F" => dgGluingCrossCoefficientFunctor R C D M
local notation "H" => dgGluingCrossHomFunctor R C D M

lemma dgGluingCrossHomCoefficientModuleMap_naturality
    (Y Z : DGGluingDFactor R C D M) :
    (F).map Y Z ≫ moduleHomPostcompose R A ((F).obj Y) ((F).obj Z) ((H).obj Z)
      (dgGluingCrossHomCoefficientModuleMap R C D M Z) =
    (H).map Y Z ≫ moduleHomPrecompose R A ((F).obj Y) ((H).obj Y) ((H).obj Z)
      (dgGluingCrossHomCoefficientModuleMap R C D M Y) := by
  apply dgGluingModuleFunctor_naturality_of_apply R A (DGGluingDFactor R C D M)
    (F) (H) (dgGluingCrossHomCoefficientModuleMap R C D M)
  intro X Y Z p q n hn g t
  rw [dgGluingCrossHomCoefficientModuleMap_eval, dgGluingCrossHomCoefficientModuleMap_eval]
  rw [dgGluingCrossCoefficientFunctor_map_apply, dgGluingCrossHomFunctor_map_apply]
  change (dgGluingCrossHomCoefficientMap R C D M X Z).f n
      (((-1 : ℤ) * p).negOnePow •
        ((moduleHomπ R C (M.rightAt Y.val.right) (M.rightAt Z.val.right) X.val.left).f p
          ((M.toFunctor.map Y.val.right Z.val.right).f p
            ((dgGluingRightHomMap R C D M Y.val Z.val).f p g))).v
          (q - 1) (n - 1) (by omega) t) =
    (p * q).negOnePow • forward R (x := X.val) (y := Y.val) (z := Z.val)
      ((dgGluingCrossHomCoefficientMap R C D M X Y).f q t) g hn
  rw [dgGluingCrossHomCoefficientMap_post R C D M X Y Z t g hn]
  have hs : (p * q).negOnePow * ((q - 1) * p).negOnePow =
      ((-1 : ℤ) * p).negOnePow := by
    rw [sub_mul, one_mul, Int.negOnePow_sub, mul_comm q p,
      ← mul_assoc, Int.units_mul_self, one_mul, neg_mul, one_mul, Int.negOnePow_neg]
  simp only [Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul, hs]

end SerrePositivity.InfinityCategories
