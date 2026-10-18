module
public import SerrePositivity.InfinityCategories.Derived.Perfect
public import SerrePositivity.InfinityCategories.Derived.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Core.HomotopyCategoryMap

/-! # Perf のホモトピー圏の充満包含

概要：Perf のホモトピー圏を h D(S) の充満部分圏として比較する。
方針：正本と dg nerve モデルの単体的同型、N3 の H⁰ 比較、充満 dg 包含を組み合わせる。
規約：ホモトピー圏は二次切断の辺の類の圏。使われ方：K 理論の入力の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：正本の Perf のホモトピー圏。
方針：二次切断の辺のホモトピー類を取る。
規約：D3 と同じ規約。使われ方：充満部分圏の比較の始域。 -/
abbrev perfectInfinityHomotopyCategory :=
  SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (perfectInfinityCategory S))

/-- 概要：正本と計算モデルのホモトピー圏は同値である。
方針：単体的同型の両方向が誘導する関手を取る。
規約：順方向は正本から計算モデルへ。使われ方：dg H⁰ との比較。 -/
def perfectModelHomotopyEquivalence : perfectInfinityHomotopyCategory S ≌
    SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (perfectNerveModel S)) :=
  CategoryTheory.Equivalence.mk (HomotopyCategoryMap.map (perfectNerveModelIso S).inv)
    (HomotopyCategoryMap.map (perfectNerveModelIso S).hom)
    (eqToIso (by
    rw [← HomotopyCategoryMap.map_comp, Iso.inv_hom_id, HomotopyCategoryMap.map_id]))
    (eqToIso (by
    rw [← HomotopyCategoryMap.map_comp, Iso.hom_inv_id, HomotopyCategoryMap.map_id]))

/-- 概要：Perf のホモトピー圏は完全 semifree dg 圏の H⁰ と同値である。
方針：計算モデルとの同値を N3 の比較に合成する。
規約：射は閉零射のホモトピー類。使われ方：充満 dg 包含による比較。 -/
def perfectInfinityH0Equivalence : perfectInfinityHomotopyCategory S ≌
    DifferentialGraded.HomotopyCategory S (PerfectSemifree S) :=
  (perfectModelHomotopyEquivalence S).trans (HomotopyComparison.equivalence S (PerfectSemifree S))

/-- 概要：Perf の H⁰ から semifree の H⁰ への充満包含。
方針：充満 dg 包含のホモトピー関手を取る。
規約：Hom 複体を保持する。使われ方：h D(S) の充満部分圏。 -/
abbrev perfectH0Inclusion :=
  (dgFullSubcategoryInclusion S (Semifree S) (perfectSemifreeProperty S)).onHomotopy

/-- 概要：h Perf(S) から h D(S) への包含比較。
方針：N3 を通して充満 dg 包含を適用する。
規約：選ばれた同値の逆関手を介して表す。使われ方：完全対象の Hom の同定。 -/
def perfectHomotopyInclusion : perfectInfinityHomotopyCategory S ⥤
    derivedInfinityHomotopyCategory S :=
  (perfectInfinityH0Equivalence S).functor ⋙ perfectH0Inclusion S ⋙
    (derivedInfinityH0Equivalence S).inverse

/-- 概要：h Perf の包含比較は充満である。
方針：N3 の同値と充満 dg 包含の充満性を合成する。
規約：全ての対象間の射を含む。使われ方：充満部分圏としての同定。 -/
instance perfectHomotopyInclusion_full : (perfectHomotopyInclusion S).Full := by
  dsimp [perfectHomotopyInclusion, perfectH0Inclusion]
  infer_instance

/-- 概要：h Perf の包含比較は忠実である。
方針：N3 の同値と充満 dg 包含の忠実性を合成する。
規約：周囲と同じホモトピー関係。使われ方：Hom 全単射。 -/
instance perfectHomotopyInclusion_faithful : (perfectHomotopyInclusion S).Faithful := by
  dsimp [perfectHomotopyInclusion, perfectH0Inclusion]
  infer_instance

end SerrePositivity.InfinityCategories
