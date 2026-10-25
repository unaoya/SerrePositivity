module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrows
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactModels

/-!
概要：強飽和生成閉包の中の周囲で compact な射に、小さい全同値模型を構成する。
方針：公開済みの全 compact 模型を生成閉包で制限し、元の小さい宇宙に縮小する。
規約：小さい模型の存在を生成性や飽和射圏の accessibility と同一視しない。
使われ方：P-1 f2、HTT 5.5.4.14 の compact な生成候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の全射圏で κ-compact であり、生成閉包に属する射の全部分圏。 -/
def compactGeneratedArrows (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) : SSet.{u + 1} :=
  fullSubcomplexOnVertices
    (Compact.kappaCompactObjects.{u, u + 1} κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (fun f ↦ arrowVertexEdge f.val ∈ generatedEdges edges)

instance compactGeneratedArrows_quasicategory (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) :
    Quasicategory (compactGeneratedArrows κ edges) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- 指定された元の compact 射を、閉包内の compact 候補圏の同じ頂点に持ち上げる。 -/
def compactGeneratedArrowVertex (κ : Cardinal.{u}) (edges : I → C _⦋1⦌)
    (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
    (hf : Compact.IsKappaCompact.{u, u + 1} κ f)
    (hs : arrowVertexEdge f ∈ generatedEdges edges) :
    (compactGeneratedArrows κ edges) _⦋0⦌ := by
  let v : (Compact.kappaCompactObjects.{u, u + 1} κ
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
    compactGeneratedArrows κ edges ⟶ generatedArrowCategory edges :=
  fullSubcomplexLift (fun f ↦ arrowVertexEdge f ∈ generatedEdges edges)
    ((fullSubcomplexOnVertices _
      (fun f : (Compact.kappaCompactObjects.{u, u + 1} κ
        ((ihom (Δ[1] : SSet.{u + 1})).obj C)) _⦋0⦌ ↦
          arrowVertexEdge f.val ∈ generatedEdges edges)).ι ≫
        Compact.kappaCompactInclusion.{u, u + 1} κ _)
    (fun f ↦ fullSubcomplexOnVertices_vertex f)

/-- 候補圏への制限は元の写像空間を保つ。 -/
lemma compactGeneratedArrowInclusion_isFullyFaithful
    (κ : Cardinal.{u}) (edges : I → C _⦋1⦌) :
    IsFullyFaithful (compactGeneratedArrowInclusion κ edges) := by
  apply (generatedArrowInclusion_isFullyFaithful edges).cancel_right
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι _ _).comp
    (Compact.kappaCompactInclusion_isFullyFaithful κ _)

/-- 周囲の全射圏が κ-accessible なら、閉包内の全 compact 射も小さい全同値模型を持つ。 -/
lemma exists_smallCompactGeneratedArrowModel {κ : Cardinal.{u}}
    (hA : IsKappaAccessible κ ((ihom (Δ[1] : SSet.{u + 1})).obj C))
    (edges : I → C _⦋1⦌) :
    ∃ (A : SSet.{u}) (hA' : Quasicategory A),
      letI := hA'
      Nonempty (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (compactGeneratedArrows κ edges)) := by
  obtain ⟨A, hA', ⟨e⟩⟩ := hA.exists_smallCompactModel
  have := hA'
  let B := Compact.kappaCompactObjects.{u, u + 1} κ
    ((ihom (Δ[1] : SSet.{u + 1})).obj C)
  let Q : B _⦋0⦌ → Prop := fun f ↦ arrowVertexEdge f.val ∈ generatedEdges edges
  let P : ((SSet.uliftFunctor.{u + 1, u}).obj A) _⦋0⦌ → Prop :=
    fun a ↦ Q (e.hom.app _ a)
  let E : SSet.{u + 1} := fullSubcomplexOnVertices _ P
  let r : E ⟶ compactGeneratedArrows κ edges :=
    fullSubcomplexLift Q ((fullSubcomplexOnVertices _ P).ι ≫ e.hom)
      (fun a ↦ fullSubcomplexOnVertices_vertex a)
  have hr : IsQCatEquivalence r := by
    refine isQCatEquivalence_fullSubcomplexRestriction P Q ?_
      e.hom e.isQCatEquivalence r rfl ?_
    · intro f g i
      exact generatedArrow_mem_iff_vertexIso edges
        ((hoFunctor.map (Compact.kappaCompactInclusion.{u, u + 1} κ _)).toFunctor.mapIso i)
    · intro a ha
      exact ha
  have hsmall (n : SimplexCategoryᵒᵖ) : Small.{u} (E.obj n) := by
    apply small_of_injective (f := fun s : E.obj n ↦ s.val.down)
    intro s t h
    apply Subtype.ext
    exact ULift.ext h
  let A₀ := smallSimplicialSet.{u, u + 1} E
  let s : (SSet.uliftFunctor.{u + 1, u}).obj A₀ ≅ E := smallSimplicialSetIso E
  have : InnerFibration s.hom := ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have := quasicategory_of_innerFibration s.hom
  have hA₀ : Quasicategory A₀ := quasicategory_of_ulift A₀
  exact ⟨A₀, hA₀, ⟨(qCatEquivalenceOfIso s).trans hr.choose⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
