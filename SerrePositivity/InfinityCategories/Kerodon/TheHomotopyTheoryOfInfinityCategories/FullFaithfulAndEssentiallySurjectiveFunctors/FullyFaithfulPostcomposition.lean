module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexFunctorFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：充満忠実な射による後合成は、任意の関手空間でも充満忠実。
方針：頂点像の全部分複体を通して同値と包含へ分解する。
規約：パラメーターの quasicategory 性は不要。
使われ方：標準 Hom の族の自然同型を元の全空間側へ回収する。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 頂点像の全部分複体への標準持ち上げは、元の充満忠実性を保つ。 -/
lemma isFullyFaithful_fullSubcomplexVertexImageLift {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift
      (fun y => ∃ x, f.app (Opposite.op ⦋0⦌) x = y) f (fun x => ⟨x, rfl⟩)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y
    (fun y => ∃ x, f.app (Opposite.op ⦋0⦌) x = y)).cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact hf

/-- 頂点像への標準持ち上げは、その全部分複体の全頂点に達する。 -/
lemma fullSubcomplexVertexImageLift_surjective {X Y : SSet.{u}} (f : X ⟶ Y) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift
      (fun y => ∃ x, f.app (Opposite.op ⦋0⦌) x = y) f
        (fun x => ⟨x, rfl⟩)).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- 充満忠実な射の頂点像への持ち上げは、実際の同じ射を順方向に持つ同値。 -/
lemma fullSubcomplexVertexImageLift_isQCatEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift
      (fun y => ∃ x, f.app (Opposite.op ⦋0⦌) x = y) f (fun x => ⟨x, rfl⟩)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · exact isFullyFaithful_fullSubcomplexVertexImageLift f hf
  · intro y
    obtain ⟨x, hx⟩ := fullSubcomplexVertexImageLift_surjective f y
    exact ⟨x, ⟨eqToIso (congrArg SSet.HomotopyCategory.mk hx)⟩⟩

/-- 任意のパラメーターを持つ関手空間で、充満忠実な射による後合成は充満忠実。 -/
lemma IsFullyFaithful.postcompose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((ihom K).map f) := by
  let P : Y _⦋0⦌ → Prop := fun y => ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P f (fun x => ⟨x, rfl⟩)
  have h : g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι = f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  rw [← h, Functor.map_comp]
  let e := (fullSubcomplexVertexImageLift_isQCatEquivalence f hf).choose.postcompose K
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (e.hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι)
  exact e.isQCatEquivalence.isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexFunctorInclusion K Y P)

/-- 充満忠実な射への後合成で得た関手同型は、元の全パラメーターの関手同型へ戻せる。 -/
def IsFullyFaithful.preimageFunctorIso {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {F G : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ f) (G ≫ f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  (hf.postcompose K).preimageVertexIso e

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
