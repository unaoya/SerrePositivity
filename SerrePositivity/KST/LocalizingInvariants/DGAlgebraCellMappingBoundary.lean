module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeConvolutionTargetTrivial
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingCellLift
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseBoundary

/-!
概要：全射擬同型な標的射は、cell 写像上で全境界に対する右持ち上げ性を持つ。
方針：全小単体の実相対制限を持ち上げ、D の境界と単体の宇宙同型で移す。
規約：零次の空境界を含み、元の上下の全単体写像を保持する。
使われ方：元の写像模型の標的擬同型不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) {X B : Mon (Complex R)}
  (q : X ⟶ B) (hs : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R q.hom) (hq : QuasiIso q.hom)
include hs hq

lemma multiplicativeCellMapping_boundary_rlp :
    SSet.modelCategoryQuillen.I.rlp
      (multiplicativeMappingPostcompose R (cellResolution R A) q) := by
  intro _ _ j hj
  obtain ⟨n⟩ := hj
  let hsmall : HasLiftingProperty
      (SSet.uliftFunctor.{u, 0}.map (SSet.boundary.{0} n).ι)
      (multiplicativeMappingPostcompose R (cellResolution R A) q) := {
    sq_hasLift := fun {a b} sq => by
      obtain ⟨c, ha, hb⟩ := multiplicativeCellMapping_small_lift R A q (SSet.boundary n).ι
        (relativeConvolutionRestriction_fibration R q _ hs)
        (relativeConvolutionRestriction_quasiIso_of_target_trivial R q _ hs hq) a b sq.w
      exact ⟨c, ha, hb⟩ }
  exact HasLiftingProperty.of_arrow_iso_left
    (Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{0, u} n) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{0, u} n)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso_ι n))
    (multiplicativeMappingPostcompose R (cellResolution R A) q) (hip := hsmall)

lemma multiplicativeCellMapping_mono_rlp :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (multiplicativeMappingPostcompose R (cellResolution R A) q) :=
  SSet.rlp_monomorphisms.ge _ (multiplicativeCellMapping_boundary_rlp R A q hs hq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
