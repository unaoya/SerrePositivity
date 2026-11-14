module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FiniteLimitsColimits

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceContractibleColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceInitial
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceProjection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteColimitPreservationGeneration
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteHornUniverseIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.PointConeSpanIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.RelativeInitialEndpoint

/-!
概要：固定始域の閉包内射圏の全有限余極限と、包含による指定余錐の保存。
方針：元の恒等射を空図式の余極限とし、標準 span は弱可縮な nerve の計算から移す。
規約：大宇宙の任意の有限単体集合を形状に許す。
使われ方：HTT 5.5.5.11 の小余完備性へ向かう有限工程。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


private def emptyCosliceIso {X : SSet.{u}} (T : SSet.{u})
    (p : (⊥ : T.Subcomplex).toSSet ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ≅ X := by
  let F : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso T X).hom (Subcomplex.isInitialBot.hom_ext _ _)
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = 𝟙 X := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.emptyJoinIso_inv, Iso.inv_hom_id]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p, F, ?_, hF⟩
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.sliceUnder_empty_hom_ext p
  rw [Category.assoc, hF, Category.comp_id, Category.id_comp]

private lemma hasPreservedEmptyColimit_of_initial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (hUx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (U.app _ x))
    (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U p := by
  let e := emptyCosliceIso T p
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := e.inv.app (Opposite.op ⦋0⦌) x
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e.symm).map_isInitialVertex hx
  have hv : c.vertex = x := by
    change ((e.inv ≫ e.hom).app (Opposite.op ⦋0⦌)) x = x
    rw [e.inv_hom_id]
    rfl
  refine ⟨c, hc, ?_⟩
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (emptyCosliceIso T (p ≫ U))).isInitialVertex_iff _).mpr
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (U.app _ c.vertex)
  rwa [hv]

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域圏の有限全図式には、全 coslice に保存される余極限がある。 -/
lemma generatedSource_hasPreservedFiniteColimit (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x) D := by
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_finite_of_empty_pointSpan U ?_ ?_ K D
  · exact hasPreservedEmptyColimit_of_initial U (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceIdentity edges x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceIdentity_isInitial edges x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex x)
  · intro p
    let e := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.uliftFiniteSpanNerveIso.{u, u + 1} ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpanIso.symm
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_restrict_isIso U p e.hom).mpr
    let z : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} := ULift.up _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanVertex.zero
    have hz : IsInitial z := IsInitial.ofUniqueHom
      (fun _ ↦ homOfLE (Or.inl rfl)) (fun _ _ ↦ Subsingleton.elim _ _)
    have hpoint : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (Δ[0] : SSet.{u}) := by
      intro n b
      exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have hJ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal hz).isWeakHomotopyEquivalence
      |>.weaklyContractible_iff.mp hpoint.isWeaklyContractible
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSource_hasNerveColimit hC edges x _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex hJ (e.hom ≫ p)

/-- 同じ固定始域圏は、元の大宇宙の全有限余極限を持つ。 -/
lemma generatedSource_hasFiniteColimits (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) := by
  constructor
  intro K hK D
  obtain ⟨c, hc, _⟩ := generatedSource_hasPreservedFiniteColimit hC edges x K D
  exact ⟨c, hc⟩

/-- 元の全 coslice への包含は、任意の指定有限余極限余錐を保存する。 -/
lemma generatedSourceInclusion_preservesFiniteColimit (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x) c) :=
  (generatedSource_hasPreservedFiniteColimit hC edges x K D).map_isColimit c hc

/-- 周囲の全 coslice の任意の指定有限余極限も、同じ閉包内に留まる。 -/
lemma generatedSource_finite_colimit_mem (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (K : SSet.{u + 1}) [K.Finite] (D : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg c.vertex (𝟙 Δ[0])).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
  obtain ⟨d, hd, hUd⟩ := generatedSource_hasPreservedFiniteColimit hC edges x K D
  have hm : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x) d).vertex
      (𝟙 Δ[0])).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex d.vertex
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCondition_iff_vertexIso edges x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceInclusion edges x) d) c hUd hc)).mp hm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
