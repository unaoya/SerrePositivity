module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMapLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：任意の準同型な実代数射を、cell 分解上で実乗法的経路を伴って持ち上げる。
方針：mapping-path の次数全射な準同型の target を使い、実 projection を合成する。
規約：元の比較射との一致は実経路で保持。使われ方：係数像への導来持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B W : Mon (Complex R)} (f : A ⟶ B)
  (hf : QuasiIso f.hom) (q : W ⟶ B)

def cellQuasiIsoPathLift : cellResolution R W ⟶ MappingPath.algebra R f :=
  cellResolutionMapLift R q (MappingPath.target R f) (MappingPath.target_surjective R f)
    (MappingPath.target_quasiIso R f hf)

lemma cellQuasiIsoPathLift_target : cellQuasiIsoPathLift R f hf q ≫ MappingPath.target R f =
    cellAugmentation R W ≫ q := cellResolutionMapLift_projection R _ _ _ _

def cellQuasiIsoLift : cellResolution R W ⟶ A :=
  cellQuasiIsoPathLift R f hf q ≫ MappingPath.projection R f

def cellQuasiIsoLiftWitness : Path.Witness R (cellQuasiIsoLift R f hf q ≫ f)
    (cellAugmentation R W ≫ q) where
  hom := cellQuasiIsoPathLift R f hf q ≫ MappingPath.inclusion R f
  source_eq := by
    rw [Category.assoc, MappingPath.condition, ← Category.assoc]
    rfl
  target_eq := cellQuasiIsoPathLift_target R f hf q

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
