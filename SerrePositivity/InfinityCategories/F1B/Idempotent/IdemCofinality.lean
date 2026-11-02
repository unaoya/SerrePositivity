module

public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1B.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.RightKanShapeIso
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking
public import SerrePositivity.InfinityCategories.F1B.Idempotent.WalkingCommaContractibility

/-!
概要：元の全 Idem の元の強い分裂添字への包含は、余極限を計算する向きに cofinal。
方針：元の comma の nerve を、元の coslice の引き戻しへ同型で移して Quillen A を使う。
規約：同じ元の包含を判定し、添字の射影への可換性も保持する。
使われ方：HTT 4.4.5.11〜12 の同じ全 Idem 図式の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の comma の nerve と元の coslice 引き戻しの、指定した比較同型。 -/
def walkingCommaCosliceIso (P : WalkingSplit.{u}) :
    nerve (StructuredArrow P walkingInclusion) ≅
      pullback idemInclusion (sliceUnderProjection (nervePoint P)) :=
  SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso P walkingInclusion ≪≫ pullbackSymmetry _ _

/-- 元の比較同型は、元の全 Idem への射影と厳密に可換。 -/
lemma walkingCommaCosliceIso_projection (P : WalkingSplit.{u}) :
    (walkingCommaCosliceIso P).hom ≫ pullback.fst idemInclusion
      (sliceUnderProjection (nervePoint P)) =
        nerveMap (StructuredArrow.proj P walkingInclusion) := by
  change (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso P walkingInclusion).hom ≫
    (pullbackSymmetry _ _).hom ≫ _ = _
  have h := pullbackSymmetry_hom_comp_fst
    (sliceUnderProjection (nervePoint P)) idemInclusion
  exact (congrArg (fun f ↦ (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso P walkingInclusion).hom ≫ f) h).trans
    (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso_hom_projection P walkingInclusion)

/-- 元の包含に沿った元の coslice の引き戻しは、各元の対象で弱可縮。 -/
lemma idemInclusion_coslice_isWeaklyContractible (P : WalkingSplit.{u}) :
    IsWeaklyContractible (pullback idemInclusion (sliceUnderProjection (nervePoint P))) := by
  have h := (isPrecompositionEquivalence_of_iso
    (walkingCommaCosliceIso P)).isWeakHomotopyEquivalence
  exact h.weaklyContractible_iff.mp (walkingComma_isWeaklyContractible P)

/-- 元の全 Idem の元の強い分裂添字への包含は、余極限を計算する向きに cofinal。 -/
lemma idemInclusion_isRightCofinal : IsRightCofinal idemInclusion.{u} := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro b
  obtain ⟨P, rfl⟩ := (nerveEquiv (C := WalkingSplit.{u})).symm.surjective b
  exact idemInclusion_coslice_isWeaklyContractible P

end SerrePositivity.InfinityCategories.F2.Idempotent
