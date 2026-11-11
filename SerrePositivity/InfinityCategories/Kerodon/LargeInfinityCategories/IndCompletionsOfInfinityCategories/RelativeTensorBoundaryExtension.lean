module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCoconeBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutProduct
/-!
概要：直積境界の可逆修正を、指定した別因子の制限を厳密に保って延長する。
方針：二つの単射の pushout-product を作り、固定境界つきの可逆円柱延長を使う。
規約：元の全境界と全修正族を保持する。
使われ方：指定始点評価を保つ全余錐比較の相対反映。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：直積の一境界を修正し、もう一境界を元の全射に厳密に固定する。
方針：pushout-product の単射性を使う。規約：指定全族を保持。使われ方：相対延長。 -/
lemma exists_extension_of_equivalenceFamily_tensor_boundary {C Q J K X : SSet.{u}} [Quasicategory X]
    (i : C ⟶ Q) [Mono i] (j : J ⟶ K) [Mono j]
    (u : Q ⊗ K ⟶ X) (v : C ⊗ K ⟶ X)
    (hv : (C ◁ j) ≫ v = (i ▷ J) ≫ (Q ◁ j) ≫ u)
    (V : (C ⊗ K) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (C ⊗ K) false ≫ V = (i ▷ K) ≫ u)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (C ⊗ K) true ≫ V = v)
    (hV : ((C ◁ j) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ V =
      fst (C ⊗ J) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ (i ▷ J) ≫ (Q ◁ j) ≫ u) :
    ∃ F : Q ⊗ K ⟶ X, (i ▷ K) ≫ F = v ∧ (Q ◁ j) ≫ F = (Q ◁ j) ≫ u := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  have : Mono sq.ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i j sq
  have hv' : (C ◁ j) ≫ v = (i ▷ J) ≫ sq.inl ≫ sq.ι ≫ u := by
    simp only [← Category.assoc, sq.inl_ι]
    convert hv using 1
    rfl
  have h₀' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint (C ⊗ K) false ≫ V = sq.inr ≫ sq.ι ≫ u := by
    simp only [← Category.assoc, sq.inr_ι]
    convert h₀ using 1
    rfl
  have hV' : ((C ◁ j) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) ≫ V =
      fst (C ⊗ J) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ (i ▷ J) ≫ sq.inl ≫ sq.ι ≫ u := by
    simp only [← Category.assoc, sq.inl_ι]
    convert hV using 1
    rfl
  obtain ⟨F, hF, hFix⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_extension_of_equivalenceFamily_fixed_boundary
    sq.isPushout.flip sq.ι u v hv' V h₀' h₁ hV'
  refine ⟨F, ?_, ?_⟩
  · simp only [← Category.assoc, sq.inr_ι] at hF
    convert hF using 1 <;> rfl
  · simp only [← Category.assoc, sq.inl_ι] at hFix
    convert hFix using 1 <;> rfl
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
