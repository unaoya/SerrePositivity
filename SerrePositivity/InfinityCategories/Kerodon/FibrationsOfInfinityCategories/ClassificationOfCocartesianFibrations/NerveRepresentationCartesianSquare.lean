module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveRepresentationComparisonLaw
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonRestriction

/-!
概要：指定witnessを保つnerve比較のcartesian制限との合成則。
方針：元の比較の値を表現空間へ戻し、既存の制限・合成の法則を使う。
規約：HTT §3.3.2・Kerodon Tag 028Tの構成の特殊な法則。別の同型を選ばない。
使われ方：P3-Dの初頂点上の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 定義済みのnerve比較の値は、同じ既存の表現空間内の比較の像である。 -/
lemma exists_nerveComparison_witness {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    ∃ a : VertexIso (transportWitnessVertex (nerveLeftTransportRepresentation p))
      (transportWitnessVertex R),
      (nerveLeftTransportRepresentation p).diagramIso R a = nerveCoherentTransportRepresentationIso p R := by
  letI (n : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u+1,u}).obj E).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u+1} (E.obj n)))
  exact ⟨smallFiberTransportRepresentationVertexIso _ (hasSmallSimplexFibers_of_small_total _)
    (nerveLeftTransportRepresentation p) R, rfl⟩

/-- 同じnerve比較は、指定した任意の表現空間内の比較から計算できる。 -/
lemma nerveComparison_of_witness {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p))
    (a : VertexIso (transportWitnessVertex (nerveLeftTransportRepresentation p))
      (transportWitnessVertex R)) :
    (nerveLeftTransportRepresentation p).diagramIso R a = nerveCoherentTransportRepresentationIso p R := by
  obtain ⟨a₀, ha₀⟩ := exists_nerveComparison_witness p R
  letI (n : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u+1,u}).obj E).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u+1} (E.obj n)))
  exact (congrArg (fun z => (nerveLeftTransportRepresentation p).diagramIso R z)
    (smallFiberTransportRepresentationVertexIso_unique _ (hasSmallSimplexFibers_of_small_total _)
      (nerveLeftTransportRepresentation p) R a a₀)).trans ha₀

/-- 元の指定cartesianな制限のnerve比較は、指定witnessとの合成を保つ。
HTT §3.3.2・Kerodon Tag 028Tの構成の、このnerve模型での特殊な法則。 -/
@[cite HTT "3.3.2" (partial := special) "指定cartesianな表現制限とnerve比較の合成則。"]
lemma nerveComparison_cartesian_witness
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E P : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (r : P ⟶ nerve D) [LeftFibration r]
    (e : P ⟶ E) (t : nerve D ⟶ nerve C)
    (h : IsPullback ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map r)
      ((SSet.uliftFunctor.{u+1,u}).map p) ((SSet.uliftFunctor.{u+1,u}).map t))
    (a : VertexIso
      (transportWitnessVertex ((nerveLeftTransportRepresentation p).cartesianRestrict
        ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map t) h))
      (transportWitnessVertex (nerveLeftTransportRepresentation r)))
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    (nerveCoherentTransportRepresentationIso p R).precomp ((SSet.uliftFunctor.{u+1,u}).map t) =
      ((nerveLeftTransportRepresentation p).cartesianRestrict
        ((SSet.uliftFunctor.{u+1,u}).map e) ((SSet.uliftFunctor.{u+1,u}).map t) h).diagramIso
        (nerveLeftTransportRepresentation r) a ≪≫
      nerveCoherentTransportRepresentationIso r
        (R.cartesianRestrict ((SSet.uliftFunctor.{u+1,u}).map e)
          ((SSet.uliftFunctor.{u+1,u}).map t) h) := by
  let U := SSet.uliftFunctor.{u+1,u}
  let R₀ := (nerveLeftTransportRepresentation p).cartesianRestrict (U.map e) (U.map t) h
  let S := R.cartesianRestrict (U.map e) (U.map t) h
  let Rr := nerveLeftTransportRepresentation r
  obtain ⟨b₀, hb₀⟩ := exists_nerveComparison_witness p R
  let b := (nerveLeftTransportRepresentation p).cartesianRestrictVertexIso R b₀
    (U.map e) (U.map t) h
  let c := a.symm ≪≫ b
  have hc : a ≪≫ c = b := by
    dsimp only [c]
    simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  calc
    _ = R₀.diagramIso S b := by
      rw [LeftTransportRepresentation.cartesianRestrict_diagramIso, hb₀]
    _ = R₀.diagramIso Rr a ≪≫ Rr.diagramIso S c := by
      rw [← LeftTransportRepresentation.diagramIso_trans, hc]
    _ = _ := congrArg (fun z => R₀.diagramIso Rr a ≪≫ z) (nerveComparison_of_witness r S c)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
