module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalPostEndpointNaturality
/-!
概要：元 lax Hom の区間模型を、矢印座標と元左右 Hom 入力の標的へ三成分同型で移す。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetLaxHomCoordinateTargetIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateTarget R C D E p q X Y := by
  letI : Limits.HasLimit (cospan
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)) := HasLimitsOfShape.has_limit _
  letI : Limits.HasLimit (cospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionEndpointPair eX eY)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)) := HasLimitsOfShape.has_limit _
  exact asIso (pullback.map _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalBaseCoordinateIso R C D E p q X Y).hom
    (by
      have h := congrArg
        (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom ≫ k)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalEndpointMap_coordinates R C D E p q X Y)
      simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h)
    (by
      have h := congrArg
        (fun k => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom ≫ k)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputMap_coordinates R C D E p q X Y)
      simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h))

lemma dgGluingHomTargetLaxHomCoordinateTargetIso_arrow :
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateArrowProjection R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalArrowProjection R C D E p q X Y ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetLaxHomCoordinateTargetIso_inputs :
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateInputsProjection R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputProjection R C D E p q X Y ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom :=
  pullback.lift_snd _ _ _

def dgGluingHomTargetLaxHomCoordinateTransport :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom

lemma dgGluingHomTargetLaxHomCoordinateTransport_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y)
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y)).mpr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPinchedIntervalTransport_equivalence R C D E p q X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
