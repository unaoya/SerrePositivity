module

public import SerrePositivity.InfinityCategories.F1.Transport.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.F1.Transport.ReverseCosliceTransportEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentOppositeIso

/-!
概要：実際の pointed-space 射影の全パラメーター付き普遍輸送は写像空間上の同値。
方針：反対 Kan 圏の nerve の反転を空間の coherent nerve へ同型で移す。
規約：既存の pointedSpaceProjection と parametrizedFiberTransport の射そのものを使う。
使われ方：Kerodon Lemma 5.6.9.1、任意の coherent 図式の境界固定の表現延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance : ∀ A B : KanObject.{u}ᵒᵖ, KanComplex (SimplicialCategory.sHom A B) :=
  fun A B ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom B.unop A.unop))

/-- 概要：反対 Kan 圏の coherent nerve の反転は空間の coherent nerve と同型。
方針：coherent nerve の反対同型の逆を反転し、二重反転を取り除く。
規約：値域は既存の SpaceInfinity。
使われ方：標準反転合成で得た普遍輸送の同値性を実際の空間の圏へ移す。 -/
def reverseKanNerveSpaceIso :
    (SimplicialNerve KanObject.{u}ᵒᵖ).op ≅ SpaceInfinity.{u} :=
  SSet.opFunctor.mapIso (HomotopyLimits.coherentNerveOppositeIso KanObject.{u}).symm ≪≫
    SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve KanObject.{u})

/-- 概要：反転 nerve の同型は反対 Kan 対象の頂点を既存の空間の頂点に送る。
方針：coherent nerve の反対同型の逆の頂点公式と二重反転を計算する。
規約：零単体の厳密な等式。
使われ方：pointed-space の始点と輸送の両端の正規化。 -/
lemma reverseKanNerveSpaceIso_vertex (K : KanObject.{u}) :
    reverseKanNerveSpaceIso.hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op K))) = spaceInfinityVertex K := by
  change SSet.opObjEquiv
    ((HomotopyLimits.coherentNerveOppositeInverse KanObject.{u}).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (Opposite.op K))) = spaceInfinityVertex K
  rw [HomotopyLimits.coherentNerveOppositeInverse_vertex, Equiv.apply_symm_apply]
  exact (spaceInfinityVertex_eq_coherent K).symm

/-- 概要：Kan 複体で表示した二頂点の間の pointed-space の普遍輸送は同値。
方針：反転底上の普遍 coslice 輸送の同値性を底と全空間の同型で移す。
規約：射影と輸送射は既存の定義のまま。
使われ方：任意の空間の二頂点での普遍輸送の同値性。 -/
lemma parametrizedPointedSpaceTransport_vertices_isQCatEquivalence (K L : KanObject.{u}) :
    IsQCatEquivalence (parametrizedFiberTransport pointedSpaceProjection
      (spaceInfinityVertex K) (spaceInfinityVertex L)) := by
  have h := parametrizedPointCosliceTransport_isQCatEquivalence_of_iso reverseKanNerveSpaceIso
    (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op pointKanObject.{u})))
    (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op K)))
    (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op L)))
    (parametrizedReverseKanPointCosliceTransport_isQCatEquivalence K L)
  rw [reverseKanNerveSpaceIso_vertex, reverseKanNerveSpaceIso_vertex,
    reverseKanNerveSpaceIso_vertex] at h
  exact h

/-- 概要：pointed-space 射影の普遍輸送は固定端点の写像空間から fiber 間の関手空間への同値。
方針：任意の空間の頂点を Kan 複体として取り出し、標準頂点の場合へ帰着する。
規約：頂点ごとの辺の輸送の同値性ではなく、全高次パラメーターに依存する射の同値性。
使われ方：Kerodon Lemma 5.6.9.1 の区間上の分類と一般の境界固定延長の入力。 -/
lemma parametrizedPointedSpaceTransport_isQCatEquivalence (s t : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (parametrizedFiberTransport pointedSpaceProjection s t) := by
  obtain ⟨K, rfl⟩ := spaceInfinityVertexEquiv.surjective s
  obtain ⟨L, rfl⟩ := spaceInfinityVertexEquiv.surjective t
  exact parametrizedPointedSpaceTransport_vertices_isQCatEquivalence K L

end SerrePositivity.InfinityCategories
