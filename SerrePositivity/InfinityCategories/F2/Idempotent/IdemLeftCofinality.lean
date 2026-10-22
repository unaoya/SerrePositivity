module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingLeftCommaContractibility
public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftKanShapeIso
public import SerrePositivity.InfinityCategories.F1B.QuillenALeft
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：元の全 Idem の元の強い分裂添字への包含は、極限を計算する向きにも cofinal。
方針：元の左 comma を元の slice の引き戻しへ同型で移し、Quillen A の left 側を使う。
規約：同じ元の包含と、元の全 Idem への射影を保持する。
使われ方：HTT 4.4.5.13 の元の強い分裂の指定錐の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の左 comma の nerve と元の slice 引き戻しの、指定した比較同型。 -/
def walkingLeftCommaSliceIso (P : WalkingSplit.{u}) :
    nerve (CostructuredArrow walkingInclusion P) ≅
      pullback idemInclusion (sliceOverProjection (nervePoint P)) :=
  F1B.kanNerveLeftKanShapeIso walkingInclusion P

/-- 元の比較同型は、元の全 Idem への射影と厳密に可換。 -/
lemma walkingLeftCommaSliceIso_projection (P : WalkingSplit.{u}) :
    (walkingLeftCommaSliceIso P).hom ≫ pullback.fst idemInclusion
      (sliceOverProjection (nervePoint P)) =
        nerveMap (CostructuredArrow.proj walkingInclusion P) :=
  F1B.kanNerveLeftKanShapeIso_hom_projection walkingInclusion P

/-- 元の包含に沿った元の slice の引き戻しは、各元の対象で弱可縮。 -/
lemma idemInclusion_slice_isWeaklyContractible (P : WalkingSplit.{u}) :
    IsWeaklyContractible (pullback idemInclusion (sliceOverProjection (nervePoint P))) := by
  have h := (isPrecompositionEquivalence_of_iso
    (walkingLeftCommaSliceIso P)).isWeakHomotopyEquivalence
  exact h.weaklyContractible_iff.mp (walkingLeftComma_isWeaklyContractible P)

/-- 元の全 Idem の元の強い分裂添字への包含は、極限を計算する向きにも cofinal。 -/
lemma idemInclusion_isLeftCofinal : IsLeftCofinal idemInclusion.{u} := by
  apply isLeftCofinal_of_weaklyContractible_slices
  intro b
  obtain ⟨P, rfl⟩ := (nerveEquiv (C := WalkingSplit.{u})).symm.surjective b
  exact idemInclusion_slice_isWeaklyContractible P

end SerrePositivity.InfinityCategories.F2.Idempotent
