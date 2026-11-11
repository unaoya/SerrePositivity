module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionInterval
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
概要：旗の解像を区間の旗へ変形する単体的ホモトピー。
方針：単位区間の頂点列に従い、各段を元の集合から区間へ広げる。
規約：最大元の射影を保つ。圏同値性そのものはここでは主張しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体上の補助射影の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単位区間の単体に従い旗の各段を区間に広げる。
方針：区間の値が零の段を保ち、それ以後の段を区間化する。
規約：始点と最大元を変えない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、区間化への変形の単体ごとの公式。 -/
def CoherentResolutionFlag.deform {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d where
  start := F.start
  sets i := if t i = 0 then F.sets i else F.intervalHull.sets i
  monotone_sets := by
    intro i j hij
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · simpa only [if_pos hi, if_pos hj] using F.monotone_sets hij
    · simpa only [if_pos hi, if_neg hj] using
        (F.monotone_sets hij).trans (F.sets_subset_intervalHull j)
    · exact False.elim (hi (le_antisymm (hj ▸ t.monotone hij) (Fin.zero_le _)))
    · simpa only [if_neg hi, if_neg hj] using F.intervalHull.monotone_sets hij
  first := by
    split
    · exact F.first
    · exact F.intervalHull.first.trans (congrArg (fun k ↦ ({k} : Finset _)) F.intervalHull_start)
  lower i k hk := by
    split at hk
    · exact F.lower i k hk
    · rw [← F.intervalHull_start]
      exact F.intervalHull.lower i k hk

/-- 概要：旗の変形は各段の最大元を保つ。
方針：段が元の集合か区間化された集合かで場合分けする。
規約：単位区間の任意の単体に適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、射影上での変形の固定性。 -/
lemma CoherentResolutionFlag.maxAt_deform {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) (i : Fin (d + 1)) :
    (F.deform t).maxAt i = F.maxAt i := by
  by_cases h : t i = 0
  · exact le_antisymm
      (F.le_maxAt i _ (by simpa only [deform, if_pos h] using (F.deform t).maxAt_mem i))
      ((F.deform t).le_maxAt i _ (by simpa only [deform, if_pos h] using F.maxAt_mem i))
  · calc
      (F.deform t).maxAt i = F.intervalHull.maxAt i := by
        apply le_antisymm
        · apply F.intervalHull.le_maxAt
          simpa only [deform, if_neg h] using (F.deform t).maxAt_mem i
        · apply (F.deform t).le_maxAt
          simpa only [deform, if_neg h] using F.intervalHull.maxAt_mem i
      _ = F.maxAt i := F.maxAt_intervalHull i

/-- 概要：旗の変形は単体の引き戻しと整合する。
方針：最大元が不変なので同じ始点で切り詰め、区間化の自然性を使う。
規約：区間の単体も同時に引き戻す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、変形を単体集合の射にする自然性。 -/
lemma CoherentResolutionFlag.deform_pullback {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.deform t).pullback α = (F.pullback α).deform (t.comp α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact F.maxAt_deform t (α 0)
  · funext i
    change (if t (α i) = 0 then F.sets (α i) else F.intervalHull.sets (α i)).filter
      (fun k ↦ (F.deform t).maxAt (α 0) ≤ k) =
      if t (α i) = 0 then (F.pullback α).sets i else (F.pullback α).intervalHull.sets i
    rw [F.maxAt_deform]
    split
    · rfl
    · have h := congrArg (fun G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n e ↦ G.sets i)
        (F.intervalHull_pullback α)
      change (F.intervalHull.sets (α i)).filter
        (fun k ↦ F.intervalHull.maxAt (α 0) ≤ k) = _ at h
      rwa [F.maxAt_intervalHull] at h

/-- 概要：零端点での旗の変形は恒等。
方針：全ての段で元の集合を選ぶ。
規約：区間の定値零単体。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、ホモトピーの始端。 -/
lemma CoherentResolutionFlag.deform_zero {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    F.deform (OrderHom.const _ 0) = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext (F := F.deform (OrderHom.const _ 0)) (G := F) rfl
  funext i
  rfl

/-- 概要：一端点での旗の変形は区間化。
方針：全ての段で区間化した集合を選ぶ。
規約：区間の定値一単体。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、ホモトピーの終端。 -/
lemma CoherentResolutionFlag.deform_one {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    F.deform (OrderHom.const _ 1) = F.intervalHull := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext (F := F.deform (OrderHom.const _ 1))
    (G := F.intervalHull) F.intervalHull_start.symm
  funext i
  rfl

/-- 概要：区間化した旗は変形の間固定される。
方針：区間化の冪等性を各段で使う。
規約：単位区間の任意の単体について成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断の像上の変形の固定性。 -/
lemma CoherentResolutionFlag.deform_intervalHull {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (t : Fin (d + 1) →o Fin 2) : F.intervalHull.deform t = F.intervalHull := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext (F := F.intervalHull.deform t) (G := F.intervalHull) rfl
  funext i
  change (if t i = 0 then F.intervalHull.sets i else F.intervalHull.intervalHull.sets i) = _
  rw [F.intervalHull_idempotent]
  split <;> rfl

/-- 概要：零次元の旗は変形の間固定される。
方針：零次元の旗の唯一の集合は始点の一点集合。
規約：変形の頂点を全て固定する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、圏的比較へ進むための頂点での固定性。 -/
lemma CoherentResolutionFlag.deform_vertex {n : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n 0)
    (t : Fin 1 →o Fin 2) : F.deform t = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext (F := F.deform t) (G := F) rfl
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact (F.deform t).first.trans F.first.symm

/-- 概要：旗の解像と単位区間の積から区間化への変形を定める。
方針：各次数で旗と区間の頂点列に変形の公式を適用する。
規約：積は単体集合の標準モノイド積。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、切断と射影の合成へのホモトピー。 -/
def coherentResolutionDeformation (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n where
  app d := ↾fun x ↦ ULift.up (x.1.down.deform x.2.down.toOrderHom)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact (x.1.down.deform_pullback x.2.down.toOrderHom α.unop.toOrderHom).symm

/-- 概要：旗の変形は最大元の射影の上で一定。
方針：各段の最大元が変形で変わらないことを使う。
規約：積の第一射影と標準単体への射影の合成で表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、底を固定したホモトピー。 -/
lemma coherentResolutionDeformation_projection (n : ℕ) :
    coherentResolutionDeformation.{u} n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.ext
  intro i
  exact x.1.down.maxAt_deform x.2.down.toOrderHom i

/-- 概要：旗の変形は全ての頂点を固定する。
方針：零次元の旗の固定性を適用する。
規約：単位区間の二つの頂点を一括して扱う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、圏的比較の頂点条件。 -/
lemma coherentResolutionDeformation_vertex (n : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⊗ Δ[1]) _⦋0⦌) :
    (coherentResolutionDeformation n).app _ x = x.1 := by
  apply ULift.ext
  exact x.1.down.deform_vertex x.2.down.toOrderHom

/-- 概要：旗の解像上で恒等から射影・切断の合成へのホモトピー。
方針：変形の零端点と一端点を計算する。
規約：単体的ホモトピーを標準の SSet.Homotopy で表す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体の旗の解像の縮約。 -/
def coherentResolutionHomotopy (n : ℕ) :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSection n) where
  h := coherentResolutionDeformation n
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact F.down.deform_zero
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact F.down.deform_one

  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
