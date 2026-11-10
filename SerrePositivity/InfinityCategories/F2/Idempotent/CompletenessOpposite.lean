module

public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingLimitExistence
public import SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle

/-!
概要：元の coherent 冪等完備性と元の retract 条件は反転で保たれる。
方針：反転した全図式の余極限を元へ戻して極限を得て、指定した図式を強く分裂する。
規約：元の二重反転同型と全 Idem の同型を使用し、同じ元の全図式を回収する。
使われ方：冪等完備化の cofinal 性の左右双対。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- coherent な元の冪等完備性は反転で保たれる。 -/
lemma IsIdempotentComplete.op {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) : IsIdempotentComplete X.op := by
  intro d
  let a := idemOppositeIso.hom ≫ SSet.opFunctor.map d
  let e := SSet.opFunctorCompOpFunctorIso.app X
  have ha : HasColimit (a ≫ e.hom) := hX.hasColimit _
  have h₁ : HasColimit a := (F1B.kanHasColimit_iff_postcomp_of_isIso a e.hom).mpr ha
  have h₂ : HasColimit (SSet.opFunctor.map d) :=
    (F1B.kanHasColimit_iff_restrict_of_isIso (SSet.opFunctor.map d)
      idemOppositeIso.hom).mpr h₁
  exact strongSplitting_exists_of_hasLimit d ((F1B.kanHasLimit_iff_hasColimit_op d).mpr h₂)

/-- 元の二点の retract の存在は、反転した同じ二点でも保たれる。 -/
lemma IsVertexRetractOf.op {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y) := by
  obtain ⟨r⟩ := h
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  have ht := compStructOp t.2.2.toTruncated
  change SSet.Truncated.Edge.CompStruct _ _
    (edgeOp (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x)) at ht
  rw [edgeOp_id] at ht
  let T : RetractionTriangle (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) :=
    ⟨SSet.Edge.ofTruncated (edgeOp t.2.1.toTruncated),
      SSet.Edge.ofTruncated (edgeOp t.1.toTruncated),
      SSet.Edge.CompStruct.ofTruncated ht⟩
  exact ⟨T.vertexRetraction⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
