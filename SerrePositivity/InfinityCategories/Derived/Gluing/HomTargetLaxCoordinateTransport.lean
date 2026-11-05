module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetLaxHomCoordinateTargetIso :
    dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ≅
      dgGluingHomTargetInputCoordinateTarget R C D E p q X Y := by
  letI : Limits.HasLimit (cospan
    (dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
    (dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)) := HasLimitsOfShape.has_limit _
  letI : Limits.HasLimit (cospan (dgGluingArrowCompositionEndpointPair eX eY)
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y ⊗ₘ
      dgGluingHomTargetRightIntervalInput R C D E p q X Y)) := HasLimitsOfShape.has_limit _
  exact asIso (pullback.map _ _ _ _
    (dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom
    (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom
    (dgGluingHomTargetLaxHomIntervalBaseCoordinateIso R C D E p q X Y).hom
    (by
      have h := congrArg
        (fun k => (dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom ≫ k)
        (dgGluingHomTargetLaxHomIntervalEndpointMap_coordinates R C D E p q X Y)
      simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h)
    (by
      have h := congrArg
        (fun k => (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom ≫ k)
        (dgGluingHomTargetLaxHomIntervalInputMap_coordinates R C D E p q X Y)
      simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h))

lemma dgGluingHomTargetLaxHomCoordinateTargetIso_arrow :
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom ≫
      dgGluingHomTargetInputCoordinateArrowProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomIntervalArrowProjection R C D E p q X Y ≫
      (dgGluingHomTargetLaxHomIntervalArrowCoordinateIso R C D E p q X Y).hom :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetLaxHomCoordinateTargetIso_inputs :
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom ≫
      dgGluingHomTargetInputCoordinateInputsProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomIntervalInputProjection R C D E p q X Y ≫
      (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).hom :=
  pullback.lift_snd _ _ _

def dgGluingHomTargetLaxHomCoordinateTransport :=
  dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y).hom

lemma dgGluingHomTargetLaxHomCoordinateTransport_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomCoordinateTransport R C D E p q X Y) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff
    (dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y)
    (dgGluingHomTargetLaxHomCoordinateTargetIso R C D E p q X Y)).mpr
    (dgGluingHomTargetLaxHomPinchedIntervalTransport_equivalence R C D E p q X Y)

end SerrePositivity.InfinityCategories
