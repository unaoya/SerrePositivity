module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedArrows
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels

/-!
概要：強飽和生成閉包の中の周囲で compact な射に、小さい全同値模型を構成する。
方針：公開済みの全 compact 模型を生成閉包で制限し、元の小さい宇宙に縮小する。
規約：小さい模型の存在を生成性や飽和射圏の accessibility と同一視しない。
使われ方：P-1 f2、HTT 5.5.4.14 の compact な生成候補。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の全射圏で κ-compact であり、生成閉包に属する射の全部分圏。 -/
def compactGeneratedArrows (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)

instance compactGeneratedArrows_quasicategory (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) :
    Quasicategory (compactGeneratedArrows κ edges) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 指定された元の compact 射を、閉包内の compact 候補圏の同じ頂点に持ち上げる。 -/
def compactGeneratedArrowVertex (κ : Cardinal.{u}) (edges : I → C _⦋1⦌)
    (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ f)
    (hs : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) :
    (compactGeneratedArrows κ edges) _⦋0⦌ := by
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ
      ((ihom (Δ[1] : SSet.{u + 1})).obj C)) _⦋0⦌ := ⟨f, by
    intro α
    have ha : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    simpa only [op_id, Functor.map_id_apply] using hf⟩
  refine ⟨v, ?_⟩
  intro α
  have ha : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst α
  simpa only [op_id, Functor.map_id_apply] using hs

/-- compact な候補の元の飽和射圏への包含。 -/
def compactGeneratedArrowInclusion (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) :
    compactGeneratedArrows κ edges ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
      (fun f : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ
        ((ihom (Δ[1] : SSet.{u + 1})).obj C)) _⦋0⦌ ↦
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges)).ι ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ _)
    (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex f)

/-- 候補圏への制限は元の写像空間を保つ。 -/
lemma compactGeneratedArrowInclusion_isFullyFaithful
    (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (compactGeneratedArrowInclusion κ edges) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowInclusion_isFullyFaithful edges).cancel_right
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful κ _)

/-- 周囲の全射圏が κ-accessible なら、閉包内の全 compact 射も小さい全同値模型を持つ。 -/
lemma exists_smallCompactGeneratedArrowModel {κ : Cardinal.{u}}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (edges : I → C _⦋1⦌) :
    ∃ (A : SSet.{u}) (hA' : Quasicategory A),
      letI := hA'
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (compactGeneratedArrows κ edges)) := by
  obtain ⟨A, hA', ⟨e⟩⟩ := hA.exists_smallCompactModel
  have := hA'
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ
    ((ihom (Δ[1] : SSet.{u + 1})).obj C)
  let Q : B _⦋0⦌ → Prop := fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges
  let P : ((SSet.uliftFunctor.{u + 1, u}).obj A) _⦋0⦌ → Prop :=
    fun a ↦ Q (e.hom.app _ a)
  let E : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P
  let r : E ⟶ compactGeneratedArrows κ edges :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift Q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ P).ι ≫ e.hom)
      (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex a)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence r := by
    refine _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.isQCatEquivalence_fullSubcomplexRestriction P Q ?_
      e.hom e.isQCatEquivalence r rfl ?_
    · intro f g i
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrow_mem_iff_vertexIso edges
        ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ _)).toFunctor.mapIso i)
    · intro a ha
      exact ha
  have hsmall (n : SimplexCategoryᵒᵖ) : Small.{u} (E.obj n) := by
    apply small_of_injective (f := fun s : E.obj n ↦ s.val.down)
    intro s t h
    apply Subtype.ext
    exact ULift.ext h
  let A₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} E
  let s : (SSet.uliftFunctor.{u + 1, u}).obj A₀ ≅ E := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso E
  have : InnerFibration s.hom := ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have := quasicategory_of_innerFibration s.hom
  have hA₀ : Quasicategory A₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.quasicategory_of_ulift A₀
  exact ⟨A₀, hA₀, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso s).trans hr.choose⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
