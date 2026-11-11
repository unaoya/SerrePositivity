module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CrossHomFunctors
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CrossHomCoefficientPreAction

/-! 同じ係数包含を、C 因子上の全 dg 自然な閉零加群射へ束ねる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M

lemma dgGluingCrossHomCoefficientFamily_naturality
    (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) (x y : Aᵒᵖ) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).obj Z).map x y ≫
      homPostcompose (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).obj Z).obj x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M y.unop Z) =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).obj Z).map x y ≫
      homPrecompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M x.unop Z)
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).obj Z).obj y) := by
  apply closedFamily_of_action R
    (M := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).obj Z)
    (N := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).obj Z)
    (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M z.unop Z)
  intro x y p r n hn f t
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M y.unop Z).f n
      (moduleAction R
        (shiftModule (-1) (restrictModule R A C
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).op (M.rightAt Z.val.right))) f t hn) =
    forward R (x := y.unop.val) (y := x.unop.val) (z := Z.val) f
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M x.unop Z).f r t) (by omega)
  unfold moduleAction
  rw [shiftModule_map_v]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M y.unop Z).f n
      (((-1 : ℤ) * p).negOnePow • moduleAction R (M.rightAt Z.val.right)
        (x := op x.unop.val.left) (y := op y.unop.val.left)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M y.unop.val x.unop.val).f p f) t
        (by omega : (r - 1) + p = n - 1)) = _
  simp only [neg_mul, one_mul, Int.negOnePow_neg]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_pre R C D M y.unop x.unop Z f t
    (by omega : p + r = n)).symm

def dgGluingCrossHomCoefficientModuleMap (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M).obj Z) ⟶
      ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M).obj Z) :=
  moduleMorphismMk R A
    (fun x => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M x.unop Z)
    (dgGluingCrossHomCoefficientFamily_naturality R C D M Z)

lemma dgGluingCrossHomCoefficientModuleMap_eval
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    (moduleEvaluation R A X).map (dgGluingCrossHomCoefficientModuleMap R C D M Z) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap R C D M X Z :=
  moduleMorphismMk_eval R A _ _ X

lemma dgGluingCrossHomCoefficientModuleMap_quasiIso
    (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    moduleQuasiIso R A (dgGluingCrossHomCoefficientModuleMap R C D M Z) := by
  intro X
  rw [dgGluingCrossHomCoefficientModuleMap_eval]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientMap_quasiIso R C D M X Z

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
