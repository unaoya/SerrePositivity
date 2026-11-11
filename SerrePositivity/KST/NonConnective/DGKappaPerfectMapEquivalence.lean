module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectYonedaNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：実 dg 射の native 同値性を、同じ射の実 Perf 延長へ移す。
方針：元の二つの Yoneda 完備化と全関手自然性から、実延長を完備化の一意性で認証する。
規約：選んだ Perf 同値を実延長射の代わりに用いない。
使われ方：K-7 e の同じ懸垂射の Morita 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

private theorem completionAfterEquivalence {X Y Z : SSet.{v}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (δ : Y ⟶ Z) (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (e.hom ≫ δ) := by
  refine ⟨hδ.1, e.isFullyFaithful.comp hδ.2.1, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hδ.2.2 y
  obtain ⟨a, ⟨ea⟩⟩ := e.isEssentiallySurjective x
  exact ⟨a, hx.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ea δ).symm)⟩

private theorem completionMapEquivalence {X Y PX PY : SSet.{v}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory PX] [Quasicategory PY]
    (δX : X ⟶ PX) (δY : Y ⟶ PY)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δX) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δY)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) (F : PX ⟶ PY)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (δX ≫ F) (e.hom ≫ δY)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence F := by
  obtain ⟨E, ⟨hE⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.equivalence_unique δX hX
    (e.hom ≫ δY) (completionAfterEquivalence e δY hY)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F E.hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general δX hX).preimageVertexIso
      (h ≪≫ hE.symm)
  exact E.isQCatEquivalence.ofFunctorIso he.symm

variable (R : Type u) [CommRing R] (C D : Type (max (u + 1) v))
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]

/-- 元始域のままの Yoneda も実 Perf への冪等完備化。 -/
theorem dgKappaPerfectYoneda_isIdempotentCompletion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R C)) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R C, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
    intro x y
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  · intro z
    obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
    obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectVertex_retract_yoneda R C M
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    exact hx

/-- 元の native 同値の実 Perf 延長自身が同値となる。 -/
theorem dgKappaPerfectMap_isQCatEquivalence (f : DGFunctor R C D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R C D f)) :=
  completionMapEquivalence _ _ (dgKappaPerfectYoneda_isIdempotentCompletion R C)
    (dgKappaPerfectYoneda_isIdempotentCompletion R D) hf.choose _
    (dgKappaPerfectYonedaNaturality R C D f)

end SerrePositivity.KST.NonConnective
