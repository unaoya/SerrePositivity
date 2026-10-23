module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredIntervalPullbackKan

/-!
概要：任意の strict Kan cospan 図式で、path 引き戻しの filtered 比較を native に構成する。
方針：実際の標準同型を可逆辺にし、元の cospan の極限錐と標準余極限余錐を合わせる。
規約：任意の coherent な filtered 図式への拡張は別工程。
使われ方：𝒮 の filtered 余極限と有限極限の交換から fibration 仮定を外す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I] [IsFiltered I] {F G H : I ⥤ SSet.{u}}
  [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] [∀ i, KanComplex (H.obj i)]
  (η : F ⟶ G) (θ : H ⟶ G)

/-- 概要：任意の二射の path 引き戻しと余極限を結ぶ native な標準比較辺。
方針：構成済みの Kan 同型を両普遍錐の実際の頂点の辺にする。
規約：終域の錐は元の cospan 上にある。使われ方：fibration 仮定なしの比較。 -/
def filteredIntervalPullbackComparisonEdge : SpaceInfinity.{u}.Edge
    (filteredKanColimitCocone (intervalPullbackKanDiagram η θ)).vertex
    (intervalPullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)).vertex :=
  (coherentNerveEdge (filteredIntervalPullbackKanIso η θ).hom).ofEq (by
    rw [filteredKanColimitCocone_vertex, spaceInfinityVertex_eq_coherent]) (by
    rw [intervalPullbackCone_vertex, spaceInfinityVertex_eq_coherent])

/-- 概要：任意の strict Kan cospan の filtered 比較辺は可逆。
方針：台の同型を弱同値・Whitehead 判定を通して coherent な可逆辺にする。
規約：元の両自然変換の fibration 性は不要。使われ方：native な交換の比較。 -/
lemma filteredIntervalPullbackComparisonEdge_isInvertible :
    IsInvertibleEdge (filteredIntervalPullbackComparisonEdge η θ) := by
  let e := filteredIntervalPullbackKanIso η θ
  let K := filteredKanColimitObject (intervalPullbackKanDiagram η θ)
  let L := intervalPullbackKanObject (filteredKanLeftMap η) (filteredKanRightMap θ)
  have : KanComplex (kanObjectForget.obj K) := K.isKanComplex
  have : KanComplex (kanObjectForget.obj L) := L.isKanComplex
  have hw := isPrecompositionEquivalence_of_iso (kanObjectForget.mapIso e)
  have he := coherentKanEdge_isInvertible_of_isQCatEquivalence (f := e.hom)
    hw.isWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence.isQCatEquivalence
  exact (isInvertibleEdge_congr (e := coherentNerveEdge e.hom)
    (f := filteredIntervalPullbackComparisonEdge η θ) rfl).mp he

/-- 概要：任意の strict Kan cospan で両側の native な普遍性と比較の可逆性を持つ。
方針：元の cospan の path 引き戻し錐と標準 filtered 余錐の普遍性を使う。
規約：元の両射の fibration 性は不要。使われ方：一般 coherent 図式の比較の基礎。 -/
lemma filteredIntervalPullbackExchange :
    IsColimitCone (filteredKanColimitCocone (intervalPullbackKanDiagram η θ)) ∧
      IsLimitCone (intervalPullbackCone (filteredKanLeftMap η) (filteredKanRightMap θ)) ∧
        IsInvertibleEdge (filteredIntervalPullbackComparisonEdge η θ) :=
  ⟨filteredKanColimitCocone_isColimit _, intervalPullbackCone_isLimit _ _,
    filteredIntervalPullbackComparisonEdge_isInvertible η θ⟩

end SerrePositivity.InfinityCategories.F2
