module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ReverseCosliceTransportEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeIso

/-!
概要：実際の pointed-space 射影の全パラメーター付き普遍輸送は写像空間上の同値。
方針：反対 Kan 圏の nerve の反転を空間の coherent nerve へ同型で移す。
規約：既存の pointedSpaceProjection と parametrizedFiberTransport の射そのものを使う。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN）、任意の coherent 図式の境界固定の表現延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance : ∀ A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ, KanComplex (SimplicialCategory.sHom A B) :=
  fun A B ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom B.unop A.unop))

/-- 概要：反対 Kan 圏の coherent nerve の反転は空間の coherent nerve と同型。
方針：coherent nerve の反対同型の逆を反転し、二重反転を取り除く。
規約：値域は既存の SpaceInfinity。
使われ方：標準反転合成で得た普遍輸送の同値性を実際の空間の圏へ移す。 -/
def reverseKanNerveSpaceIso :
    (SimplicialNerve _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).symm ≪≫
    SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})

/-- 概要：反転 nerve の同型は反対 Kan 対象の頂点を既存の空間の頂点に送る。
方針：coherent nerve の反対同型の逆の頂点公式と二重反転を計算する。
規約：零単体の厳密な等式。
使われ方：pointed-space の始点と輸送の両端の正規化。 -/
lemma reverseKanNerveSpaceIso_vertex (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    reverseKanNerveSpaceIso.hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op K))) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K := by
  change SSet.opObjEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op K))) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeInverse_vertex, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent K).symm

/-- 概要：Kan 複体で表示した二頂点の間の pointed-space の普遍輸送は同値。
方針：反転底上の普遍 coslice 輸送の同値性を底と全空間の同型で移す。
規約：射影と輸送射は既存の定義のまま。
使われ方：任意の空間の二頂点での普遍輸送の同値性。 -/
lemma parametrizedPointedSpaceTransport_vertices_isQCatEquivalence (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedPointCosliceTransport_isQCatEquivalence_of_iso reverseKanNerveSpaceIso
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u})))
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op K)))
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op L)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedReverseKanPointCosliceTransport_isQCatEquivalence K L)
  rw [reverseKanNerveSpaceIso_vertex, reverseKanNerveSpaceIso_vertex,
    reverseKanNerveSpaceIso_vertex] at h
  exact h

/-- 概要：pointed-space 射影の普遍輸送は固定端点の写像空間から fiber 間の関手空間への同値。
方針：任意の空間の頂点を Kan 複体として取り出し、標準頂点の場合へ帰着する。
規約：頂点ごとの辺の輸送の同値性ではなく、全高次パラメーターに依存する射の同値性。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の区間上の分類と一般の境界固定延長の入力。 -/
lemma parametrizedPointedSpaceTransport_isQCatEquivalence (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s t) := by
  obtain ⟨K, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertexEquiv.surjective s
  obtain ⟨L, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertexEquiv.surjective t
  exact parametrizedPointedSpaceTransport_vertices_isQCatEquivalence K L

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
