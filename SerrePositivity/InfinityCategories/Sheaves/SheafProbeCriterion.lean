module

public import SerrePositivity.InfinityCategories.Sheaves.SieveProbeLocality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DetectingFamily

/-!
概要：小さい検出族で全被覆篩のテンソル辺を試して層条件を判定する。
方針：G8の一辺の局所性、指定切断辺の判定、G14の検出性を合成する。
使われ方：HTT 5.5.4.15・6.2.2.7、Kerodon Tag 06VH の層生成辺。
規約：検出族の自然性を追加仮定にしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 全被覆篩の元のテンソル辺に関する局所性は、元の層条件と一致する。 -/
lemma isSheaf_iff_probe_locality (J : GrothendieckTopology C) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {ι : Type u} (M : ι → E _⦋0⦌) (hM : IsDetectingFamily M) (F : Presheaf C E) :
    IsSheaf J F ↔ ∀ (U : C) (S : Sieve U), S ∈ J U → ∀ i,
      IsQCatEquivalence (precompose (functorVertex F)
        (Truncated.HomotopyCategory.homMk (SetWeight.sieveTensorEdge S hE (M i)).toTruncated)) := by
  rw [isSheaf_iff_sieveSectionsMap_isInvertible J hE F]
  constructor
  · intro h U S hS i
    have he := h U S hS
    have hp := (hM (Truncated.HomotopyCategory.homMk
      (sectionsOf_map S.functorInclusion F
        (sectionsOfDiagram_hasLimit hE S.functor F)
        (sectionsOfDiagram_hasLimit hE (yoneda.obj U) F)).toTruncated)).mp he i
    exact (sieveTensorEdge_locality_iff S hE (M i) F
      (sectionsOfCone S.functor F _) (sectionsOfCone_isLimit _ _ _)
      (sectionsOfCone (yoneda.obj U) F _) (sectionsOfCone_isLimit _ _ _)).mpr hp
  · intro h U S hS
    apply (hM (Truncated.HomotopyCategory.homMk
      (sectionsOf_map S.functorInclusion F
        (sectionsOfDiagram_hasLimit hE S.functor F)
        (sectionsOfDiagram_hasLimit hE (yoneda.obj U) F)).toTruncated)).mpr
    intro i
    exact (sieveTensorEdge_locality_iff S hE (M i) F
      (sectionsOfCone S.functor F _) (sectionsOfCone_isLimit _ _ _)
      (sectionsOfCone (yoneda.obj U) F _) (sectionsOfCone_isLimit _ _ _)).mp (h U S hS i)

end SerrePositivity.InfinityCategories.Sheaves
