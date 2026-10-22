module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomFunctors
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficientPreAction

/-! 同じ係数包含を、C 因子上の全 dg 自然な閉零加群射へ束ねる。 -/
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

lemma dgGluingCrossHomCoefficientFamily_naturality
    (Z : DGGluingDFactor R C D M) (x y : Aᵒᵖ) :
    ((dgGluingCrossCoefficientFunctor R C D M).obj Z).map x y ≫
      homPostcompose (((dgGluingCrossCoefficientFunctor R C D M).obj Z).obj x)
        (dgGluingCrossHomCoefficientMap R C D M y.unop Z) =
    ((dgGluingCrossHomFunctor R C D M).obj Z).map x y ≫
      homPrecompose (dgGluingCrossHomCoefficientMap R C D M x.unop Z)
        (((dgGluingCrossHomFunctor R C D M).obj Z).obj y) := by
  apply closedFamily_of_action R
    (M := (dgGluingCrossCoefficientFunctor R C D M).obj Z)
    (N := (dgGluingCrossHomFunctor R C D M).obj Z)
    (fun z => dgGluingCrossHomCoefficientMap R C D M z.unop Z)
  intro x y p r n hn f t
  change (dgGluingCrossHomCoefficientMap R C D M y.unop Z).f n
      (moduleAction R
        (shiftModule (-1) (restrictModule R A C
          (dgGluingCFactorProjection R C D M).op (M.rightAt Z.val.right))) f t hn) =
    forward R (x := y.unop.val) (y := x.unop.val) (z := Z.val) f
      ((dgGluingCrossHomCoefficientMap R C D M x.unop Z).f r t) (by omega)
  unfold moduleAction
  rw [shiftModule_map_v]
  change (dgGluingCrossHomCoefficientMap R C D M y.unop Z).f n
      (((-1 : ℤ) * p).negOnePow • moduleAction R (M.rightAt Z.val.right)
        (x := op x.unop.val.left) (y := op y.unop.val.left)
        ((dgGluingLeftHomMap R C D M y.unop.val x.unop.val).f p f) t
        (by omega : (r - 1) + p = n - 1)) = _
  simp only [neg_mul, one_mul, Int.negOnePow_neg]
  exact (dgGluingCrossHomCoefficientMap_pre R C D M y.unop x.unop Z f t
    (by omega : p + r = n)).symm

def dgGluingCrossHomCoefficientModuleMap (Z : DGGluingDFactor R C D M) :
    ForgetEnrichment.of (Complex R) ((dgGluingCrossCoefficientFunctor R C D M).obj Z) ⟶
      ForgetEnrichment.of (Complex R) ((dgGluingCrossHomFunctor R C D M).obj Z) :=
  moduleMorphismMk R A
    (fun x => dgGluingCrossHomCoefficientMap R C D M x.unop Z)
    (dgGluingCrossHomCoefficientFamily_naturality R C D M Z)

lemma dgGluingCrossHomCoefficientModuleMap_eval
    (X : DGGluingCFactor R C D M) (Z : DGGluingDFactor R C D M) :
    (moduleEvaluation R A X).map (dgGluingCrossHomCoefficientModuleMap R C D M Z) =
      dgGluingCrossHomCoefficientMap R C D M X Z :=
  moduleMorphismMk_eval R A _ _ X

lemma dgGluingCrossHomCoefficientModuleMap_quasiIso
    (Z : DGGluingDFactor R C D M) :
    moduleQuasiIso R A (dgGluingCrossHomCoefficientModuleMap R C D M Z) := by
  intro X
  rw [dgGluingCrossHomCoefficientModuleMap_eval]
  exact dgGluingCrossHomCoefficientMap_quasiIso R C D M X Z

end SerrePositivity.InfinityCategories
