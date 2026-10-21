module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathEndpointsSurjective
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathEndpointsQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMapLift

/-!
概要：全射準同型の上で一致する二つの実代数射を、cell 分解上の相対経路で結ぶ。
方針：構成した相対二端点射の全射準同型性に、実 cell 代数持ち上げを適用する。
規約：元の源は明示的な cell augmentation で置き換える。使われ方：導来写像比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {A C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  (f g : A ⟶ C) (h : f ≫ p = g ≫ p)

def cellPathLift : cellResolution R A ⟶ algebra R p :=
  cellResolutionMapLift R (endpointsLift R p f g h) (endpointsMap R p)
    (endpointsMap_surjective R p) (endpointsMap_quasiIso R p hs hq)

lemma cellPathLift_endpointsMap : cellPathLift R p hs hq f g h ≫ endpointsMap R p =
    cellAugmentation R A ≫ endpointsLift R p f g h :=
  cellResolutionMapLift_projection R _ _ _ _

lemma cellPathLift_source : cellPathLift R p hs hq f g h ≫ source R p =
    cellAugmentation R A ≫ f := by
  calc
    _ = cellPathLift R p hs hq f g h ≫ (endpointsMap R p ≫ endpointsSource R p) := by
      rw [endpointsMap_source]
    _ = _ := by
      rw [← Category.assoc, cellPathLift_endpointsMap, Category.assoc,
        endpointsLift_source]

lemma cellPathLift_target : cellPathLift R p hs hq f g h ≫ target R p =
    cellAugmentation R A ≫ g := by
  calc
    _ = cellPathLift R p hs hq f g h ≫ (endpointsMap R p ≫ endpointsTarget R p) := by
      rw [endpointsMap_target]
    _ = _ := by
      rw [← Category.assoc, cellPathLift_endpointsMap, Category.assoc,
        endpointsLift_target]

lemma cellPathLift_projection : cellPathLift R p hs hq f g h ≫ projection R p =
    cellAugmentation R A ≫ f ≫ p := by
  rw [← source_projection, ← Category.assoc, cellPathLift_source, Category.assoc]

def cellPathWitness : Path.Witness R (cellAugmentation R A ≫ f) (cellAugmentation R A ≫ g) where
  hom := cellPathLift R p hs hq f g h ≫ inclusion R p
  source_eq := by
    rw [Category.assoc]
    exact cellPathLift_source R p hs hq f g h
  target_eq := by
    rw [Category.assoc]
    exact cellPathLift_target R p hs hq f g h

lemma cellPathWitness_relative :
    (cellPathWitness R p hs hq f g h).hom ≫ Path.map R p =
      (cellAugmentation R A ≫ f ≫ p) ≫ Path.diagonal R B := by
  change (cellPathLift R p hs hq f g h ≫ inclusion R p) ≫ Path.map R p = _
  rw [Category.assoc, condition, ← Category.assoc, cellPathLift_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
