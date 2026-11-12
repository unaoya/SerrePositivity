module
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroMap
public import SerrePositivity.KST.SConstruction.SInterchangeEvaluations
public import SerrePositivity.KST.SConstruction.ObjectSVertices

/-! # 元の object S の辺と三角圏 K₀ の関係
概要：元の object S₁ の評価対象の三角圏 K₀ 類は、退化辺と S₂ の関係を満たす。
方針：元の cofiber 正方形の三角形と、三つの S₁ 面の厳密な回収を使う。
規約：実際の BF K 群の単射性に依存しない。使われ方：K₀ 比較の逆写像の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Pretriangulated SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の object S₁ の辺に、その評価対象の三角圏 K₀ 類を対応させる。 -/
def objectTriangulatedClass (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) : TriangulatedK0 (hoFunctor.obj X.carrier) :=
  TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
    (SSet.HomotopyCategory.mk ((sOneComparison X.carrier).app _ e))

/-- 元の cofiber 図式の頂点の評価は、その実際の正方形の同じ角の評価。 -/
lemma cofiberStableEvaluation_vertex (X : StableModel.{u})
    (v : (cofiberDiagrams X.carrier) _⦋0⦌)
    (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    (cofiberStableEvaluation X a).val.app (Opposite.op ⦋0⦌) v =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val).app (Opposite.op ⦋0⦌) a := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X.carrier).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X.carrier) a).app (Opposite.op ⦋0⦌) v.val = _
  exact (congrArg (fun w => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X.carrier) a).app
    (Opposite.op ⦋0⦌) w) hv).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex a (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val))

/-- 元の S₁ 評価は実際の gapped 図式の非対角成分。 -/
lemma sOneComparison_gappedDiagram_vertex (C : SSet.{u})
    (d : (sConstruction 1 C) _⦋0⦌) :
    (sOneComparison C).app (Opposite.op ⦋0⦌) d =
      (gappedDiagram d).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide))) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram d) = d.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
  rw [sOneComparison_eq_evaluation]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C)
    (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide)))).app (Opposite.op ⦋0⦌) d.val = _
  rw [← hv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]

/-- 元の任意の cofiber 正方形の対象の三角圏 K₀ 類は加法関係を満たす。 -/
lemma cofiberTriangulatedClass_additivity (X : StableModel.{u})
    (v : (cofiberDiagrams X.carrier) _⦋0⦌) :
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableMiddle X).val.app _ v)) =
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableSubobject X).val.app _ v)) +
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableQuotient X).val.app _ v)) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X.carrier := ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val, hv.1⟩
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t := hv.2
  have hT : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht ∈ distTriang (hoFunctor.obj X.carrier) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht
  change TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableEvaluation X
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0)).val.app _ v)) =
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableEvaluation X
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)).val.app _ v)) +
    TriangulatedK0.mk (C := hoFunctor.obj X.carrier)
      (SSet.HomotopyCategory.mk ((cofiberStableEvaluation X
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)).val.app _ v))
  rw [cofiberStableEvaluation_vertex, cofiberStableEvaluation_vertex,
    cofiberStableEvaluation_vertex]
  exact TriangulatedK0.mk_triangle (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht) hT

/-- 三角圏 K₀ の対象類は元の S₂ の三辺の加法関係を満たす。 -/
lemma objectTriangulatedClass_sTwo (X : StableModel.{u})
    (q : (objectSConstruction X.carrier) _⦋2⦌) :
    objectTriangulatedClass X ((objectSConstruction X.carrier).δ 1 q) =
      objectTriangulatedClass X ((objectSConstruction X.carrier).δ 2 q) +
        objectTriangulatedClass X ((objectSConstruction X.carrier).δ 0 q) := by
  unfold objectTriangulatedClass
  rw [sTwoFace_middle, sTwoFace_subobject, sTwoFace_quotient]
  exact cofiberTriangulatedClass_additivity X ((sTwoCofiberRestriction X.carrier).app _ q)

/-- 元の零段からの退化辺の評価対象は零対象。 -/
lemma sOneComparison_degenerate_isZero (X : StableModel.{u})
    (z : (objectSConstruction X.carrier) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sOneComparison X.carrier).app _ ((objectSConstruction X.carrier).σ 0 z)) := by
  let d := (objectSConstruction X.carrier).σ 0 z
  have he : gappedDiagram d = arNerveMap (SimplexCategory.σ (0 : Fin 1)).toOrderHom ≫
      gappedDiagram z := gappedDiagram_objectS_map (SimplexCategory.σ (0 : Fin 1)).op z
  rw [sOneComparison_gappedDiagram_vertex, he]
  have ha : (arNerveMap (SimplexCategory.σ (0 : Fin 1)).toOrderHom).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide))) =
        ComposableArrows.mk₀ (arObj (0 : Fin 1) 0 le_rfl) := rfl
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, ha]
  exact (gappedDiagram_isGapped (z : (sConstruction 0 X.carrier) _⦋0⦌)).1 0

/-- 三角圏 K₀ の対象類は元の退化辺で零となる。 -/
lemma objectTriangulatedClass_degenerate (X : StableModel.{u})
    (z : (objectSConstruction X.carrier) _⦋0⦌) :
    objectTriangulatedClass X ((objectSConstruction X.carrier).σ 0 z) = 0 :=
  TriangulatedK0.mk_of_isZero _ (sOneComparison_degenerate_isZero X z).isZeroHo

end SerrePositivity.KST.SConstruction
