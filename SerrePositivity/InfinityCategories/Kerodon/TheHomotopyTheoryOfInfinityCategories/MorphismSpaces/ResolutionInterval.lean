module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionSimplex
public import Mathlib.Order.Interval.Finset.Fin

/-!
概要：区間の旗による標準単体の解像の切断。
方針：単調な頂点列の最初の頂点と各頂点の間の閉区間を旗にする。
規約：切断は固定した標準単体 n に対して構成する。n に関する自然性は主張しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の補助射影の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単調な頂点列から最初の頂点を左端とする区間の旗を作る。
方針：各段を閉区間 [f(0),f(i)] とする。
規約：包含順序で増大する旗。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体の旗の解像への切断。 -/
def CoherentResolutionFlag.interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d where
  start := f 0
  sets i := Finset.Icc (f 0) (f i)
  monotone_sets := by
    intro i j hij k hk
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hl, hr.trans (f.monotone hij)⟩
  first := Finset.Icc_self _
  lower i k hk := (Finset.mem_Icc.mp hk).1

/-- 概要：区間の旗の最大元は元の頂点列。
方針：閉区間の右端の所属と上界性を使う。
規約：左端が右端以下であることは単調性で保証する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断と射影の合成の計算。 -/
lemma CoherentResolutionFlag.maxAt_interval {n d : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (i : Fin (d + 1)) :
    (CoherentResolutionFlag.interval f).maxAt i = f i := by
  apply le_antisymm
  · exact (Finset.mem_Icc.mp ((CoherentResolutionFlag.interval f).maxAt_mem i)).2
  · apply (CoherentResolutionFlag.interval f).le_maxAt
    exact Finset.mem_Icc.mpr ⟨f.monotone (Fin.zero_le i), le_rfl⟩

/-- 概要：区間の旗を引き戻すと引き戻した頂点列の区間の旗。
方針：最初に選んだ頂点で区間を切り詰めると新しい閉区間になる。
規約：任意の単調写像に対して成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断の単体的な自然性。 -/
lemma CoherentResolutionFlag.interval_pullback {n d e : ℕ}
    (f : Fin (d + 1) →o Fin (n + 1)) (α : Fin (e + 1) →o Fin (d + 1)) :
    (CoherentResolutionFlag.interval f).pullback α =
      CoherentResolutionFlag.interval (f.comp α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · change (CoherentResolutionFlag.interval f).maxAt (α 0) = f (α 0)
    exact CoherentResolutionFlag.maxAt_interval f (α 0)
  · funext i
    apply Finset.ext
    intro k
    change k ∈ (Finset.Icc (f 0) (f (α i))).filter
      (fun l ↦ (CoherentResolutionFlag.interval f).maxAt (α 0) ≤ l) ↔
        k ∈ Finset.Icc (f (α 0)) (f (α i))
    rw [CoherentResolutionFlag.maxAt_interval]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have h0 := f.monotone (Fin.zero_le (α 0))
    exact ⟨fun ⟨⟨_, hr⟩, hl⟩ ↦ ⟨hl, hr⟩,
      fun ⟨hl, hr⟩ ↦ ⟨⟨h0.trans hl, hr⟩, hl⟩⟩

/-- 概要：標準単体から旗の解像への区間による切断。
方針：単体の頂点列を区間の旗に写し、引き戻しの整合性を使う。
規約：次数 n を固定した単体集合の射。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の射影の逆候補。 -/
def coherentResolutionSection (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n where
  app d := ↾fun s ↦ ULift.up (CoherentResolutionFlag.interval s.down.toOrderHom)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact (CoherentResolutionFlag.interval_pullback s.down.toOrderHom α.unop.toOrderHom).symm

/-- 概要：区間の切断の後に最大元の射影を取ると恒等になる。
方針：各単体の各頂点で区間の最大元を計算する。
規約：同型ではなく切断の式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の比較の一方の合成。 -/
lemma coherentResolutionSection_projection (n : ℕ) :
    coherentResolutionSection.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact CoherentResolutionFlag.maxAt_interval s.down.toOrderHom i

/-- 概要：旗の各集合を同じ最大元を持つ区間に広げる。
方針：各段の最大元の単調列から区間の旗を作る。
規約：最大元と最初の頂点を保つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、もう一方の合成と恒等を比較するホモトピー。 -/
def CoherentResolutionFlag.intervalHull {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d := CoherentResolutionFlag.interval ⟨F.maxAt, F.maxAt_monotone⟩

/-- 概要：区間化した旗の始点は元の始点。
方針：最初の段の最大元を計算する。
規約：全次数の旗に適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、区間化へのホモトピーの端点。 -/
lemma CoherentResolutionFlag.intervalHull_start {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    F.intervalHull.start = F.start := F.maxAt_zero

/-- 概要：区間化は元の旗の各集合を含む。
方針：始点の下界性と各段の最大元の上界性を使う。
規約：包含方向に広げる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、区間化へのホモトピーの単調性。 -/
lemma CoherentResolutionFlag.sets_subset_intervalHull {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (i : Fin (d + 1)) :
    F.sets i ⊆ F.intervalHull.sets i := by
  intro k hk
  apply Finset.mem_Icc.mpr
  change F.maxAt 0 ≤ k ∧ k ≤ F.maxAt i
  rw [F.maxAt_zero]
  exact ⟨F.lower i k hk, F.le_maxAt i k hk⟩

/-- 概要：区間化した旗の最大元は元の最大元。
方針：区間の旗の最大元の計算を使う。
規約：全ての段で同じ頂点列を持つ。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、射影上で固定されたホモトピーの準備。 -/
lemma CoherentResolutionFlag.maxAt_intervalHull {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (d + 1)) : F.intervalHull.maxAt i = F.maxAt i :=
  CoherentResolutionFlag.maxAt_interval _ _

/-- 概要：区間化は旗の引き戻しに自然。
方針：区間の旗の引き戻し則と、最大元の引き戻し則を組み合わせる。
規約：面と退化の両方を含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、区間化へのホモトピーの単体的な自然性。 -/
lemma CoherentResolutionFlag.intervalHull_pullback {n d e : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    F.intervalHull.pullback α = (F.pullback α).intervalHull := by
  change (CoherentResolutionFlag.interval ⟨F.maxAt, F.maxAt_monotone⟩).pullback α =
    CoherentResolutionFlag.interval ⟨(F.pullback α).maxAt, (F.pullback α).maxAt_monotone⟩
  rw [CoherentResolutionFlag.interval_pullback]
  congr 1
  ext i
  exact congrArg Fin.val (F.maxAt_pullback α i).symm

/-- 概要：区間化を二回行っても一回と同じ旗。
方針：区間化が各段の最大元を保つことを使う。
規約：区間の旗は区間化の下で固定される。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断と射影の合成の固定性。 -/
lemma CoherentResolutionFlag.intervalHull_idempotent {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) : F.intervalHull.intervalHull = F.intervalHull := by
  change CoherentResolutionFlag.interval ⟨F.intervalHull.maxAt, F.intervalHull.maxAt_monotone⟩ =
    CoherentResolutionFlag.interval ⟨F.maxAt, F.maxAt_monotone⟩
  congr 1
  ext i
  exact congrArg Fin.val (F.maxAt_intervalHull i)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
