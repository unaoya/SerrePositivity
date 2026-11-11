module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：同型不変な頂点条件へ制限した同値は同値。
方針：包含の充満忠実性で写像空間を比較し、本質的全射性を頂点条件で制限する。
規約：始域の条件を標的の条件から反映することを明示的に要求する。
使われ方：全相対 Hom の同値を cocartesian 関手の全部分複体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 標的の同型不変な頂点条件を反映する全部分複体への制限は、元の同値を保つ。 -/
lemma isQCatEquivalence_fullSubcomplexRestriction {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hQ : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (Q x ↔ Q y))
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f)
    (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q)
    (hr : r ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ f)
    (hP : ∀ x, Q (f.app (Opposite.op ⦋0⦌) x) → P x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence r := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y Q).cancel_right
    rw [hr]
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι X P).comp hf.isFullyFaithful
  · intro y
    obtain ⟨x, ⟨e⟩⟩ := hf.choose.isEssentiallySurjective y.val
    have hx : P x := hP x ((hQ e).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y))
    let x' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌ := ⟨x, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      subst α
      simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    refine ⟨x', ⟨(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y Q).preimageVertexIso ?_⟩⟩
    have he := congrArg (fun k => k.app (Opposite.op ⦋0⦌) x') hr
    change (r.app (Opposite.op ⦋0⦌) x').val = f.app (Opposite.op ⦋0⦌) x at he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (r.app (Opposite.op ⦋0⦌) x').val y.val
    rw [he]
    exact e

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
