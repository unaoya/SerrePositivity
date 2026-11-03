module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakExtension
public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakEndpoints
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingClassification
public import SerrePositivity.InfinityCategories.F1.Idempotent.StrongSplittingColimit
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping

/-!
概要：冪等完備な元の全部分圏の対象の retract は、同型を除いて元の部分圏内に戻る。
方針：元の retract の弱い全図式を延長し、その同じ全 Idem 図式を全部分圏で強く分裂する。
規約：元の指定頂点を保ち、同じ全図式の余極限の一意性で実際の頂点同型を得る。
使われ方：HTT 5.1.4.8 の本質像の retract 閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 冪等完備な元の全部分圏の対象の指定 retract は、元の部分圏の対象と同型。 -/
lemma retract_iso_in_complete_fullSubcomplex {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : IsIdempotentComplete (fullSubcomplexOnVertices X P))
    (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) (y : X _⦋0⦌)
    (r : VertexRetraction y x.val) :
    ∃ z : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌, Nonempty (VertexIso y z.val) := by
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  obtain ⟨F, hF⟩ := weakDiagram_extension_exists t.weakDiagram
  have hs : F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingSource) = x.val := by
    have h := t.weakDiagram_sourcePoint
    rw [← hF, ← Category.assoc, weakComparison_sourcePoint] at h
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h
  have hy : F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingImage) = y := by
    have h := t.weakDiagram_imagePoint
    rw [← hF, ← Category.assoc, weakComparison_imagePoint] at h
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h
  let d := idemInclusion ≫ F
  have hd : ∀ v : IdemShape.{u} _⦋0⦌, P (d.app (Opposite.op ⦋0⦌) v) := by
    intro v
    obtain ⟨a, rfl⟩ := (nerveEquiv (C := WalkingIdem.{u})).symm.surjective v
    obtain rfl := walkingObject_eq a
    change P (F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingSource))
    rw [hs]
    exact fullSubcomplexOnVertices_vertex x
  let d' := fullSubcomplexLift P d hd
  obtain ⟨s'⟩ := hP d'
  let s : StrongSplitting d := ⟨s'.val ≫ (fullSubcomplexOnVertices X P).ι, by
    rw [← Category.assoc, s'.property]
    exact fullSubcomplexLift_ι P d hd⟩
  let sF : StrongSplitting d := ⟨F, rfl⟩
  have e := VertexIso.map (initialVertexIso sF.cocone_isColimit s.cocone_isColimit)
    (sliceUnderProjection d)
  change VertexIso sF.cocone.vertex s.cocone.vertex at e
  rw [StrongSplitting.cocone_vertex, StrongSplitting.cocone_vertex] at e
  have ey : sF.vertex = y := hy
  refine ⟨s'.vertex, ⟨?_⟩⟩
  change VertexIso y s.vertex
  exact ey ▸ e

end SerrePositivity.InfinityCategories.F2.Idempotent
