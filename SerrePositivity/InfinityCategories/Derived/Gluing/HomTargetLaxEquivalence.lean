module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxHomEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxVertices
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：元 Hom gluing の指定比較自身の充満忠実性と本質的全射性から、元二脚への全同値を構成する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetNerveLaxComparison_isFullyFaithful :
    IsFullyFaithful (dgGluingHomTargetNerveLaxComparison R C D E p q) :=
  (dgGluingHomTargetNerveLaxComparison_fullyFaithful_iff R C D E p q).mpr
    (fun X Y => dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y)

lemma dgGluingHomTargetNerveLaxComparison_isQCatEquivalence :
    IsQCatEquivalence (dgGluingHomTargetNerveLaxComparison R C D E p q) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgGluingHomTargetNerveLaxComparison_isFullyFaithful R C D E p q)
    (dgGluingHomTargetNerveLaxComparison_isEssentiallySurjective R C D E p q)

def dgGluingHomTargetNerveLaxEquivalence :
    QCatEquivalence (dgNerve R (DGGluingObject R C D M))
      (F2.laxPullback (dgNerve.map p) (dgNerve.map q)) :=
  (dgGluingHomTargetNerveLaxComparison_isQCatEquivalence R C D E p q).choose

lemma dgGluingHomTargetNerveLaxEquivalence_hom :
    (dgGluingHomTargetNerveLaxEquivalence R C D E p q).hom =
      dgGluingHomTargetNerveLaxComparison R C D E p q := rfl

end SerrePositivity.InfinityCategories
