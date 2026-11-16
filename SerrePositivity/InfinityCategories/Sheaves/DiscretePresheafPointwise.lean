module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafEssentialImage
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.EssentialImageDiagram
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.SmallNerveDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpaceCoherentRepresentation

/-!
概要：離散前層の本質像を、点ごとの離散性で判定する。
方針：既存の充満忠実な離散埋め込みの本質像に図式を持ち上げ、通常前層を読み戻す。
  文献対応：HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）、S8 の離散層化への入力。
規約：型は drafts/Sheaves/SpaceValued の元の型。点ごとの同型からの新しい貼り合わせを作らない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 離散前層の本質像は各点で離散。HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）。 -/
lemma Is0Truncated.pointwise {x : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌}
    (hx : Is0Truncated x) (U : C) :
    Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U)))) := by
  obtain ⟨P, ⟨e⟩⟩ := hx
  let q := evaluateFunctorAt (X := presheafShape C) (Y := SpaceInfinity.{u}) (ULift.up (nerveVertex (Opposite.op U)))
  have ev := e.map q
  have hv : functorVertex (vertexToPresheaf x) = x :=
    (functorVertexEquiv _ _).apply_symm_apply x
  have hs : q.app (Opposite.op ⦋0⦌) x =
      (vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U))) :=
    (congrArg (q.app (Opposite.op ⦋0⦌)) hv.symm).trans
      (evaluateFunctorAt_functorVertex _ _)
  change VertexIso (q.app (Opposite.op ⦋0⦌) x)
    (q.app (Opposite.op ⦋0⦌) (functorVertex (discretePresheaf P))) at ev
  rw [hs] at ev
  dsimp only [q] at ev
  rw [evaluateFunctorAt_functorVertex, discretePresheaf_vertex] at ev
  exact ⟨P.obj (Opposite.op U), ⟨by simpa only [discreteSpaceInclusion_vertex] using ev⟩⟩

/-- 点ごとに離散な同じ全図式は、既存の離散埋め込みの始域の図式として回収できる。
HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）、既存の本質像持ち上げの特殊化。 -/
lemma exists_setDiagram_of_pointwise_discrete (F : Presheaf C SpaceInfinity.{u})
    (h : ∀ U : C, Is0TruncatedSpace (F.app _ (ULift.up (nerveVertex (Opposite.op U))))) :
    ∃ r : presheafShape C ⟶ nerve (Type u), Nonempty (FunctorIso (r ≫ discreteSpaceInclusion) F) := by
  apply exists_diagram_in_fullyFaithful_source discreteSpaceInclusion
    discreteSpaceInclusion_isFullyFaithful F
  intro k
  obtain ⟨T, ⟨e⟩⟩ := h (Opposite.unop (k.down.obj 0))
  refine ⟨nerveVertex T, ⟨?_⟩⟩
  have hk : ULift.up (nerveVertex (k.down.obj 0)) = k := by
    apply ULift.ext
    exact ComposableArrows.ext₀ rfl
  simpa only [hk] using e.symm

/-- 同じ集合値前層の通常 nerve 表示を離散埋め込みで送ると元の離散前層全体になる。
HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）、既存の図式実現の合成則。 -/
lemma smallNerveDiagram_discrete (P : Cᵒᵖ ⥤ Type u) :
    smallNerveDiagram P ≫ discreteSpaceInclusion = discretePresheaf P := by
  rw [discreteSpaceInclusion_eq_coherent]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 元の離散前層の本質像は点ごとの離散性で判定できる。
HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）。型は drafts の元の点ごとの判定。 -/
theorem is0Truncated_iff_pointwise (x : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌) :
    Is0Truncated x ↔ ∀ U : C,
      Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U)))) := by
  constructor
  · exact fun hx U => hx.pointwise U
  · intro h
    obtain ⟨r, ⟨e⟩⟩ := exists_setDiagram_of_pointwise_discrete (vertexToPresheaf x) h
    let P := smallNerveFunctor r
    have er : FunctorIso (discretePresheaf P) (vertexToPresheaf x) := by
      rw [← smallNerveDiagram_discrete, smallNerveDiagram_read]
      exact e
    have hv : functorVertex (vertexToPresheaf x) = x :=
      (functorVertexEquiv _ _).apply_symm_apply x
    exact ⟨P, ⟨hv ▸ er.symm⟩⟩

end SerrePositivity.InfinityCategories.Sheaves
