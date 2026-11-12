module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarMaurerCartanCriterion
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
/-!
概要：D の公開 MC 方程式から、元の coherent bar の実右 dg 加群を作る。
方針：同じ graded 直和と dgCoherentBarTheta を moduleMaurerCartan に渡す。
規約：MC は元の全 Hom の等式そのものを仮定し、別の微分や模型に置換しない。
使われ方：D-bar の native 余錐と評価比較で使う実 bar 加群の固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarMaurerCartan : Prop :=
  (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) +
    compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)
      (show (1 : ℤ) + 1 = 2 from rfl) = 0

def dgCoherentBarModule (hMC : dgCoherentBarMaurerCartan R D F) : RightModule R D :=
  _root_.SerrePositivity.DifferentialGraded.moduleMaurerCartan R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) hMC

variable (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarModule_X (x : Dᵒᵖ) (n : ℤ) :
    ((dgCoherentBarModule R D F hMC).obj x).X n =
      ((ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).obj x).X n := rfl

lemma dgCoherentBarModule_d (x : Dᵒᵖ) (n : ℤ) :
    ((dgCoherentBarModule R D F hMC).obj x).d n (n + 1) =
      ((ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).obj x).d n (n + 1) +
      ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) x.unop).f 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F)).v n (n + 1) rfl :=
  _root_.SerrePositivity.DifferentialGraded.maurerCartanPerturbComplex_d _ _
    (_root_.SerrePositivity.DifferentialGraded.moduleMaurerCartan_evaluation R D _ _ hMC x.unop) n

lemma dgCoherentBarModule_map_v (x y : Dᵒᵖ) (p : ℤ)
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    (((dgCoherentBarModule R D F hMC).map x y).f p a).v i j hij =
      (((ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).map x y).f p a).v
        i j hij := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
