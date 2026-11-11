module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingColimit
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：冪等完備な元の全部分圏の対象の retract は、同型を除いて元の部分圏内に戻る。
方針：元の retract の弱い全図式を延長し、その同じ全 Idem 図式を全部分圏で強く分裂する。
規約：元の指定頂点を保ち、同じ全図式の余極限の一意性で実際の頂点同型を得る。
使われ方：HTT 5.1.4.8 の本質像の retract 閉性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 冪等完備な元の全部分圏の対象の指定 retract は、元の部分圏の対象と同型。 -/
lemma retract_iso_in_complete_fullSubcomplex {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P))
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) (y : X _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction y x.val) :
    ∃ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso y z.val) := by
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_extension_exists t.weakDiagram
  have hs : F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource) = x.val := by
    have h := t.weakDiagram_sourcePoint
    rw [← hF, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_sourcePoint] at h
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h
  have hy : F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) = y := by
    have h := t.weakDiagram_imagePoint
    rw [← hF, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_imagePoint] at h
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ F
  have hd : ∀ v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} _⦋0⦌, P (d.app (Opposite.op ⦋0⦌) v) := by
    intro v
    obtain ⟨a, rfl⟩ := (nerveEquiv (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u})).symm.surjective v
    obtain rfl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject_eq a
    change P (F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource))
    rw [hs]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  let d' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P d hd
  obtain ⟨s'⟩ := hP d'
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d := ⟨s'.val ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι, by
    rw [← Category.assoc, s'.property]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P d hd⟩
  let sF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d := ⟨F, rfl⟩
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertexIso sF.cocone_isColimit s.cocone_isColimit)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection d)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso sF.cocone.vertex s.cocone.vertex at e
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting.cocone_vertex] at e
  have ey : sF.vertex = y := hy
  refine ⟨s'.vertex, ⟨?_⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso y s.vertex
  exact ey ▸ e

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
