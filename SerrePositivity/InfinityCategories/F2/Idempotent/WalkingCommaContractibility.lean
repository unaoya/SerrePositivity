module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingSourceComma
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemWeakContractibility

/-!
概要：元の分裂添字の各対象から元の冪等包含への comma の nerve は弱可縮。
方針：非分裂対象では指定した始対象で収縮し、分裂対象では元の圏同型を使う。
規約：元の comma に Kan 性を要求せず、同じ射影を通る比較を使う。
使われ方：HTT 4.4.5.11 の Quillen A 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の非分裂対象からの comma は、指定した始対象により弱可縮。 -/
lemma walkingSourceComma_isWeaklyContractible :
    IsWeaklyContractible (nerve (StructuredArrow walkingSource.{u} walkingInclusion)) := by
  let η : (Functor.const (StructuredArrow walkingSource walkingInclusion)).obj
      walkingSourceCommaPoint ⟶ 𝟭 _ :=
    { app c := walkingSourceComma_isInitial.to c
      naturality _ _ _ := walkingSourceComma_isInitial.hom_ext _ _ }
  have H := F1B.kanNerveNatTransHomotopy η
  rw [F1B.kanNerveMap_const] at H
  let g : (⊤_ SSet.{u}) ⟶ nerve (StructuredArrow walkingSource walkingInclusion) :=
    SSet.const (nerveVertex walkingSourceCommaPoint)
  have he : IsSimplicialHomotopyEquivalence
      (terminal.from (nerve (StructuredArrow walkingSource walkingInclusion))) := by
    refine ⟨g, ?_, ?_⟩
    · change Nonempty (SSet.Homotopy (_ ≫ SSet.const _) (𝟙 _))
      rw [SSet.comp_const]
      exact ⟨H⟩
    · have h : g ≫ terminal.from _ = 𝟙 _ := terminal.hom_ext _ _
      rw [h]
      exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩
  exact he.isWeakHomotopyEquivalence

/-- 元の分裂対象からの comma は、元の Idem との圏同型により弱可縮。 -/
lemma walkingImageComma_isWeaklyContractible :
    IsWeaklyContractible (nerve (StructuredArrow walkingImage.{u} walkingInclusion)) := by
  let e : nerve (StructuredArrow walkingImage walkingInclusion) ≅ IdemShape.{u} :=
    nerveFunctor.mapIso walkingImageCommaIso
  have h := (qCatEquivalenceOfIso e).isQCatEquivalence
  exact h.isWeakHomotopyEquivalence.weaklyContractible_iff.mpr idemShape_isWeaklyContractible

/-- 元の分裂添字の任意の対象からの comma は弱可縮。 -/
lemma walkingComma_isWeaklyContractible (P : WalkingSplit.{u}) :
    IsWeaklyContractible (nerve (StructuredArrow P walkingInclusion)) := by
  rcases walkingSplit_object_cases P with h | h
  · subst P
    exact walkingSourceComma_isWeaklyContractible
  · subst P
    exact walkingImageComma_isWeaklyContractible

end SerrePositivity.InfinityCategories.F2.Idempotent
