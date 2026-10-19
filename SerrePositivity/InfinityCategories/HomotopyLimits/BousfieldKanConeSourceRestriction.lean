module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanConePointSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSourceWeightedRestriction

/-!
概要：Kan coend の錐全体上の明示的な Hom の族を、既存の coend 比較と同定する。
方針：普遍点の weighted な切断と前合成の一致へ還元し、全パラメータの評価を計算する。
規約：同じ始域と終域を持つ同値性だけでなく、比較射そのものを照合する。
使われ方：HTT 4.2.4.1 の余極限性の制限条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 錐全体上の明示的な族の制限は、Kan coend の既存の反転 Hom 比較に一致する。 -/
lemma bousfieldKanCoherentConeSourceFamily_restrict (F : I ⥤ KanObject.{u})
    (Y : KanObject.{u}) :
    coherentConeSourceFamily (bousfieldKanCoherentOppositeCone F)
        (Opposite.op (kanReflectedBousfieldKanColimitObject F))
        (bousfieldKanCoherentOppositeCone_vertex F) (Opposite.op Y) ≫
      coneSectionRestriction (bousfieldKanCoherentOppositeCone F)
        (coherentNerveVertex (Opposite.op Y)) = bousfieldKanCoherentConeComparison F Y := by
  apply relativeFunctorUncurry_injective
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex (Opposite.op Y))))
    (strictCoherentDiagram F.op)
  rw [coherentConeSourceFamily_restriction_weighted F.op _ _ _
    (bousfieldKanConeWeightedPointSection F)
    (bousfieldKanCoherentOppositeCone_cosliceSection_weighted F)]
  rw [bousfieldKanCoherentConeComparison_uncurry]
  simp only [← Category.assoc]
  congr 1
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  change (ULift.up
      ((bousfieldKanWeightedNerveEvaluation
        (simplicialHomDiagram F.op
          (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)).app
            (Opposite.op ⦋n⦌)
              (((inv (fst _ (Δ[0] : SSet.{u + 1}))).app
                (Opposite.op ⦋n⦌) σ).1.down, ((bousfieldKanLiftedEndPoint F).app (Opposite.op ⦋n⦌)
                ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).2).down)),
        s) =
    (ULift.up
      ((bousfieldKanWeightedNerveEvaluation
        (simplicialHomDiagram F.op
          (Opposite.op (kanReflectedBousfieldKanColimitObject F)) ⋙ SSet.opFunctor)).app
            (Opposite.op ⦋n⦌)
              (σ.down, (kanReflectedBousfieldKanColimitHomPoint F).app
                (Opposite.op ⦋n⦌) PUnit.unit)), s)
  have hf := ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id
      (fst ((SSet.uliftFunctor.{u + 1, u}).obj (nerve Iᵒᵖ))
        (Δ[0] : SSet.{u + 1}))) (Opposite.op ⦋n⦌)) σ
  change ((inv (fst _ (Δ[0] : SSet.{u + 1}))).app (Opposite.op ⦋n⦌) σ).1 = σ at hf
  rw [hf]
  congr 3
  simp only [bousfieldKanLiftedEndPoint, SSet.yonedaEquiv_symm_zero]
  congr 1
  change PinchedHom.constant
    ((kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌) PUnit.unit) n =
      (kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋n⦌) PUnit.unit
  exact (unitHom_app_constant (kanReflectedBousfieldKanColimitHomPoint F) n).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
