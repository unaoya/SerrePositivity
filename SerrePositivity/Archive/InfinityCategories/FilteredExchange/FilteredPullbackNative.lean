module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredPullbackKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：各段の一脚が fibration の strict Kan 図式で、filtered 余極限と引き戻しを native に比較する。
方針：通常の比較同型を coherent な可逆辺にし、既存の両普遍性と合わせる。
規約：任意の coherent な図式への拡張と一般の二射の path 模型への接続は別工程。
使われ方：𝒮 の filtered 余極限と有限極限の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：N の native な引き戻し錐の頂点は元の Kan 引き戻し対象。
方針：図式の cast と strict 錐の頂点の式を使う。
規約：左脚に fibration 性を仮定する。使われ方：比較辺の端点。 -/
lemma spacePullbackCone_vertex {E B D : KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)
    [Fibration (show E.obj ⟶ B.obj from p)] :
    (spacePullbackCone p q).vertex = spaceInfinityVertex (kanPullbackCone p q).pt := by
  rw [spacePullbackCone, JoinCone.vertex_cast, strictCoherentCone_vertex,
    spaceInfinityVertex_eq_coherent]

variable {I : Type u} [SmallCategory I] [IsFiltered I] {F G H : I ⥤ SSet.{u}}
  [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] [∀ i, KanComplex (H.obj i)]
  (η : F ⟶ G) (θ : H ⟶ G) [∀ i, Fibration (η.app i)]

/-- 概要：引き戻し図式の余極限と、余極限の引き戻しを結ぶ SpaceInfinity の辺。
方針：構成済みの標準同型を coherent nerve の辺にする。
規約：両端は実際の余極限余錐と極限錐の頂点。使われ方：native な交換の比較。 -/
def filteredPullbackComparisonEdge : SpaceInfinity.{u}.Edge
    (filteredKanColimitCocone (kanDiagramOfSSet (pullback η θ))).vertex
    (spacePullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)).vertex :=
  (coherentNerveEdge (filteredKanPullbackColimitIso η θ).hom).ofEq (by
    rw [filteredKanColimitCocone_vertex, spaceInfinityVertex_eq_coherent]) (by
    rw [spacePullbackCone_vertex, spaceInfinityVertex_eq_coherent])

/-- 概要：native な引き戻しの filtered 比較辺は可逆。
方針：台の実際の同型の弱同値性を coherent な可逆性へ移す。
規約：比較辺そのものを扱う。使われ方：余極限と極限の交換。 -/
lemma filteredPullbackComparisonEdge_isInvertible :
    IsInvertibleEdge (filteredPullbackComparisonEdge η θ) := by
  let e := filteredKanPullbackColimitIso η θ
  let K := filteredKanColimitObject (kanDiagramOfSSet (pullback η θ))
  let L := (kanPullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)).pt
  have : KanComplex (kanObjectForget.obj K) := K.isKanComplex
  have : KanComplex (kanObjectForget.obj L) := L.isKanComplex
  have hw := (isPrecompositionEquivalence_of_iso (kanObjectForget.mapIso e))
  have he := coherentKanEdge_isInvertible_of_isQCatEquivalence (f := e.hom)
    hw.isWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence.isQCatEquivalence
  exact (isInvertibleEdge_congr (e := coherentNerveEdge e.hom)
    (f := filteredPullbackComparisonEdge η θ) rfl).mp he

/-- 概要：一脚 fibration の strict Kan 図式では両側の native な普遍性と比較の可逆性を持つ。
方針：標準の filtered 余錐・引き戻し錐の普遍性と比較辺の可逆性を合わせる。
規約：元の通常の図式を保持する。使われ方：一般の path 置換への拡張の基礎。 -/
lemma filteredFibrationPullbackExchange :
    IsColimitCone (filteredKanColimitCocone (kanDiagramOfSSet (pullback η θ))) ∧
      IsLimitCone (spacePullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)) ∧
        IsInvertibleEdge (filteredPullbackComparisonEdge η θ) :=
  ⟨filteredKanColimitCocone_isColimit _, spacePullbackCone_isLimitCone _ _,
    filteredPullbackComparisonEdge_isInvertible η θ⟩

end SerrePositivity.InfinityCategories.F2
