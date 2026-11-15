module

public import SerrePositivity.InfinityCategories.Sheaves.SheafGeneratingEdges
public import SerrePositivity.InfinityCategories.Sheaves.LocalEdgeRepresentative
public import SerrePositivity.InfinityCategories.Sheaves.SheafProbeCriterion

/-!
概要：被覆篩の元のテンソル辺族による局所対象が層に一致し、層化反射が存在する。
方針：G8の指定四角形とG14の検出族を使い、既存のBousfield反射へ渡す。
使われ方：HTT 5.5.4.15・6.2.2.7、Kerodon Tag 06VH。
規約：一般presentable係数で、安定性やCAlgの忘却との両立を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 小さい生成辺族の局所性は指定した層条件と一致する。 -/
lemma isLocalObject_sheafGeneratingEdges_iff (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) {ι : Type u} (M : ι → E _⦋0⦌) (hM : IsDetectingFamily M)
    (F : (PresheafCat C E) _⦋0⦌) :
    IsLocalObject (Set.range (sheafGeneratingEdges J hE M)) F ↔ sheafProperty J F := by
  have hv : functorVertex (vertexToPresheaf F) = F :=
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply F
  constructor
  · intro h
    apply (isSheaf_iff_probe_locality J hE M hM (vertexToPresheaf F)).mpr
    intro U S hS i
    rw [hv]
    apply (localForEdgeRepresentative_iff
      (SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveTensorEdge S hE (M i)) F).mp
    exact h _ ⟨⟨U, ⟨S, hS⟩, i⟩, rfl⟩
  · intro h e he
    rcases he with ⟨⟨U, ⟨S, hS⟩, i⟩, rfl⟩
    have hp := (isSheaf_iff_probe_locality J hE M hM (vertexToPresheaf F)).mp h U S hS i
    rw [hv] at hp
    exact (localForEdgeRepresentative_iff
      (SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveTensorEdge S hE (M i)) F).mpr hp

/-- 任意の小さいsiteとpresentable係数について、層をちょうど検出する小さい辺族。 -/
theorem exists_sheafGeneratingEdges (J : GrothendieckTopology C) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ (I : Type u) (edges : I → (PresheafCat C E) _⦋1⦌),
      ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F := by
  obtain ⟨ι, M, hM⟩ := exists_detectingFamily hE
  exact ⟨_, sheafGeneratingEdges J hE M, isLocalObject_sheafGeneratingEdges_iff J hE M hM⟩

/-- 一般presentable係数に対し、層への実際の反射が存在する。 -/
theorem sheafification_exists (J : GrothendieckTopology C) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    Sheafification J E := by
  obtain ⟨I, edges, hW⟩ := exists_sheafGeneratingEdges J hE
  exact sheafification_of_generatingEdges J hE edges hW

end SerrePositivity.InfinityCategories.Sheaves
