module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingSourceLeftComma
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemWeakContractibility

/-!
概要：元の分裂添字の各対象への元の冪等包含の comma の nerve は弱可縮。
方針：非分裂対象では指定した終対象で収縮し、分裂対象では元の圏同型を使う。
規約：元の comma に Kan 性を要求せず、同じ射影を通る比較を使う。
使われ方：HTT 4.4.5.13 の Quillen A 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の非分裂対象への comma は、指定した終対象により弱可縮。 -/
lemma walkingSourceLeftComma_isWeaklyContractible :
    IsWeaklyContractible (nerve (CostructuredArrow walkingInclusion walkingSource.{u})) := by
  let η : 𝟭 (CostructuredArrow walkingInclusion walkingSource) ⟶
      (Functor.const _).obj walkingSourceLeftCommaPoint :=
    { app c := walkingSourceLeftComma_isTerminal.from c
      naturality _ _ _ := walkingSourceLeftComma_isTerminal.hom_ext _ _ }
  have H := F1B.kanNerveNatTransHomotopy η
  rw [F1B.kanNerveMap_const] at H
  let g : (⊤_ SSet.{u}) ⟶ nerve (CostructuredArrow walkingInclusion walkingSource) :=
    SSet.const (nerveVertex walkingSourceLeftCommaPoint)
  apply isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from _) g
  · change SSet.Homotopy (𝟙 _) (_ ≫ SSet.const _)
    rw [SSet.comp_const]
    exact H
  · have h : g ≫ terminal.from _ = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

/-- 元の分裂対象への comma は、元の Idem との圏同型により弱可縮。 -/
lemma walkingImageLeftComma_isWeaklyContractible :
    IsWeaklyContractible (nerve (CostructuredArrow walkingInclusion walkingImage.{u})) := by
  let e : nerve (CostructuredArrow walkingInclusion walkingImage) ≅ IdemShape.{u} :=
    nerveFunctor.mapIso walkingImageLeftCommaIso
  have h := (qCatEquivalenceOfIso e).isQCatEquivalence
  exact h.isWeakHomotopyEquivalence.weaklyContractible_iff.mpr idemShape_isWeaklyContractible

/-- 元の分裂添字の任意の対象への comma は弱可縮。 -/
lemma walkingLeftComma_isWeaklyContractible (P : WalkingSplit.{u}) :
    IsWeaklyContractible (nerve (CostructuredArrow walkingInclusion P)) := by
  rcases walkingSplit_object_cases P with h | h
  · subst P
    exact walkingSourceLeftComma_isWeaklyContractible
  · subst P
    exact walkingImageLeftComma_isWeaklyContractible

end SerrePositivity.InfinityCategories.F2.Idempotent
