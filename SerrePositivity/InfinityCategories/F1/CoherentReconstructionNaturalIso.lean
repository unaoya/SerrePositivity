module

public import SerrePositivity.InfinityCategories.F1.CoherentReconstructionHomRecovery
public import SerrePositivity.InfinityCategories.F1.OppositeFunctorIso

/-!
概要：元の left fibrations の全空間で、weighted nerve による復元自己関手と恒等を比較する。
方針：全 Hom の族から回収した同型を、coherent nerve と単体集合の二つの反転で戻す。
規約：指定された元の復元自己関手を保持し、対象ごとの厳密化の自然性は仮定しない。
使われ方：strict transport と分類図式の自然な単位の主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

local instance {B : SSet.{u}} :
    ∀ X Y : (LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 元の全 left fibrations の恒等関手と weighted nerve の復元自己関手の自然な同型。 -/
def leftStrictTransportReconstructionNaturalIso (C : Type u) [Category.{u} C] :
    FunctorIso (𝟙 (LeftFibrationInfinity (nerve C)))
      (coherentNerveMap (strictTransportWeightedEnriched C)) := by
  let e := HomotopyLimits.coherentNerveOppositeIso (LeftFibrationObject (nerve C))
  let F := strictTransportWeightedEnriched C
  have hn : SSet.opFunctor.map (coherentNerveMap F) ≫ e.hom =
      e.hom ≫ coherentNerveMap (simplicialEnrichedOpposite F) :=
    HomotopyLimits.coherentNerveOppositeMap_post F
  have hr : e.hom ≫ coherentNerveMap (simplicialEnrichedOpposite F) ≫ e.inv =
      SSet.opFunctor.map (coherentNerveMap F) := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := ((leftStrictTransportReconstructionOppositeIso C).precomp e.hom).postcomp e.inv
  change FunctorIso ((e.hom ≫ 𝟙 _) ≫ e.inv)
    ((e.hom ≫ coherentNerveMap (simplicialEnrichedOpposite F)) ≫ e.inv) at h
  simp only [Category.assoc, Category.id_comp, Iso.hom_inv_id, hr] at h
  have n : FunctorIso (SSet.opFunctor.map (𝟙 (LeftFibrationInfinity (nerve C))))
      (SSet.opFunctor.map (coherentNerveMap F)) := by
    change FunctorIso (SSet.opFunctor.map (𝟙 (LeftFibrationInfinity (nerve C))))
      (SSet.opFunctor.map (coherentNerveMap F)) at h
    exact h
  exact n.unop

/-- 同じ全空間の復元同型の、実際の単体的ホモトピー。 -/
def leftStrictTransportReconstructionNaturalHomotopy (C : Type u) [Category.{u} C] :
    SSet.Homotopy (𝟙 (LeftFibrationInfinity (nerve C)))
      (coherentNerveMap (strictTransportWeightedEnriched C)) :=
  (leftStrictTransportReconstructionNaturalIso C).simplicialHomotopy

/-- 復元同型の終域は、元の strict transport、図式の包含、weighted nerve の合成そのもの。 -/
lemma strictTransportWeightedEnriched_coherentMap (C : Type u) [Category.{u} C] :
    coherentNerveMap (strictTransportWeightedEnriched C) =
      leftStrictTransportInfinityMap C ≫ coherentNerveMap strictTransportKanDiagramEnriched ≫
        weightedNerveInfinityMap C := rfl

/-- 実際の三つの比較射による全空間の復元は、恒等関手と自然に同型。 -/
def leftStrictTransportWeightedNerveNaturalIso (C : Type u) [Category.{u} C] :
    FunctorIso (𝟙 (LeftFibrationInfinity (nerve C)))
      (leftStrictTransportInfinityMap C ≫ coherentNerveMap strictTransportKanDiagramEnriched ≫
        weightedNerveInfinityMap C) := by
  rw [← strictTransportWeightedEnriched_coherentMap]
  exact leftStrictTransportReconstructionNaturalIso C

/-- 全空間の同じ復元自己関手そのものは同値であり、対象ごとの逆を必要としない。 -/
lemma strictTransportWeightedEnriched_coherentMap_isQCatEquivalence
    (C : Type u) [Category.{u} C] :
    IsQCatEquivalence (coherentNerveMap (strictTransportWeightedEnriched C)) :=
  IsQCatEquivalence.ofFunctorIso
    (qCatEquivalenceOfIso (Iso.refl (LeftFibrationInfinity (nerve C)))).isQCatEquivalence
    (leftStrictTransportReconstructionNaturalIso C)

end SerrePositivity.InfinityCategories
