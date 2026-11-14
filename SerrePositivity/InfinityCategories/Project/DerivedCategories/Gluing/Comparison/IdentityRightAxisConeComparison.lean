module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetConeInrNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ZeroSourceModuleConeIso
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisHom
public import SerrePositivity.KST.SConstruction.DGStandardClosedComparisonIso
public import SerrePositivity.KST.SConstruction.DGStandardFunctorIsoReflection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
/-!
概要：閉零対象による恒等 Hom gluing の実右軸上で、元 cone 関手を同じ Yoneda に全比較する。
方針：元 cone 右包含の実同型と全 Hom 自然性を、標準 DK と native nerve の比較へ移す。
規約：元の右包含を順射に保持。使われ方：恒等 cone 差の局所化試験圏での回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C] [Small.{u} C]
  (z : C) (hz : IsZero (ForgetEnrichment.of (Complex R) z))
local notation "I" => DGFunctor.id (A := R) C
local notation "M" => dgHomGluingBimodule R C C C I I
local notation "J" => dgGluingRightAxis R C C M z hz
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingIdentityRightAxisYoneda_eq :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightYoneda R C C C I I)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgYoneda R C) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightYoneda
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id,
    Category.comp_id, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    dgGluingRightAxis_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id, Category.id_comp]

def dgGluingIdentityRightAxisConeModuleIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgYoneda R C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgHomGluingModuleConeFunctor R C C C I I))) := by
  let F := (J).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightYoneda R C C C I I)
  let G := (J).comp (dgHomGluingModuleConeFunctor R C C C I I)
  let e (x : C) : ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (G.obj x) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.zeroSourceModuleConeIso R C (dgHomGluingTargetModuleMap R C C C I I ((J).obj x))
      ((dgYoneda R C).onClosed.map_isZero hz)
  have he (x y : C) : F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (e y).hom =
    G.map x y ≫ eHomWhiskerRight (Complex R) (e x).hom
      (ForgetEnrichment.of (Complex R) (G.obj y)) := by
    have h := congrArg (fun k => (J).map x y ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetConeInr_naturality R C C C I I ((J).obj x) ((J).obj y))
    change ((J).map x y ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightYoneda R C C C I I).map
        ((J).obj x) ((J).obj y)) ≫ _ =
      ((J).map x y ≫ (dgHomGluingModuleConeFunctor R C C C I I).map
        ((J).obj x) ((J).obj y)) ≫ _
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  have h := dgStandardFunctorIso_to_native (dgStandardClosedComparisonIso F G e he)
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h (dgGluingIdentityRightAxisYoneda_eq R C z hz) rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
