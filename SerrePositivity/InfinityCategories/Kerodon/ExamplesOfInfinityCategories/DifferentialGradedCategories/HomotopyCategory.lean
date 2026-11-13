module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import Mathlib.CategoryTheory.Equivalence

/-! # dg nerve のホモトピー圏と dg 圏の H⁰ の同値

概要：二次切断の辺のホモトピー類による圏を、既存の dg 圏の H⁰ と比較する。
方針：辺を閉零射へ送り、境界関係による商へ降ろす。合成の比較で関手性を確認する。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：導来 ∞ 圏のホモトピー圏の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open CategoryTheory.SimplicialObject.Truncated
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：dg nerve の二次切断から定義するホモトピー圏。
方針：Mathlib の辺の左ホモトピー類による圏を使う。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：H⁰ との比較の源。 -/
abbrev nerveHomotopyCategory := SSet.Truncated.HomotopyCategory₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D)

/-- 概要：辺のホモトピー類を閉零射の境界類へ送る関手。
方針：辺と境界関係の比較により商に降ろし、恒等辺と実際の合成の三角形で関手性を示す。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：ホモトピー圏から H⁰ への比較。 -/
def toH0 : nerveHomotopyCategory A D ⥤ HomotopyCategory A D where
  obj x := (toHomotopy A D).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.vertexClosed x.pt)
  map {x y} := _root_.Quotient.lift
    (fun f : SSet.Truncated.Edge x.pt y.pt => (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f))
    (fun f g h => (toHomotopy_map_eq_iff A D _ _).mpr ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicL_iff_boundary f g).mp h))
  map_id x := by
    change (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (SSet.Truncated.Edge.id x.pt)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosed_id]
    exact (toHomotopy A D).map_id _
  map_comp := by
    intro x y z f g
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro f g
    change (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (f.comp g)) =
      (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f) ≫ (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed g)
    have h := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicL_iff_boundary (f.comp g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.strictComp f g)).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.comp_homotopic_strictComp f g)
    rw [(toHomotopy_map_eq_iff A D _ _).mpr h, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosed_strictComp, Functor.map_comp]

/-- 概要：比較関手は辺の代表元を対応する閉零射の境界類に送る。
方針：商上の関数の代表元での定義を評価する。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：比較関手の計算と充満性・忠実性。 -/
lemma toH0_homMk {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂} (f : SSet.Truncated.Edge x y) :
    (toH0 A D).map (SSet.Truncated.HomotopyCategory₂.homMk f) =
      (toHomotopy A D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f) := rfl

/-- 概要：比較関手は忠実。
方針：H⁰ での同一視が境界関係であることから、元の辺が左ホモトピックであることを得る。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：比較関手から圏同値を構成する。 -/
instance toH0_faithful : (toH0 A D).Faithful where
  map_injective {x y} f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro f g h
    exact _root_.Quotient.sound ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicL_iff_boundary f g).mpr
      ((toHomotopy_map_eq_iff A D _ _).mp h))

/-- 概要：比較関手は充満。
方針：H⁰ の射の閉零代表元を取り、辺と閉零射の同値の逆で辺の代表元を作る。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：比較関手から圏同値を構成する。 -/
instance toH0_full : (toH0 A D).Full where
  map_surjective {x y} f := by
    obtain ⟨g, hg⟩ := (toHomotopy A D).map_surjective f
    refine ⟨SSet.Truncated.HomotopyCategory₂.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv x.pt y.pt).symm g), ?_⟩
    rw [toH0_homMk]
    have h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv x.pt y.pt).symm g) = g :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv x.pt y.pt).apply_symm_apply g
    rw [h]
    exact hg

/-- 概要：比較関手は本質的全射。
方針：H⁰ の任意の対象を、その dg 対象の定値零単体の像として表す。
規約：HA Example 1.3.1.8。使われ方：比較関手から圏同値を構成する。 -/
instance toH0_essSurj : (toH0 A D).EssSurj where
  mem_essImage y :=
    ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) y.as)⟩, ⟨eqToIso rfl⟩⟩

/-- 概要：ホモトピー圏から H⁰ への比較関手は圏同値を与える。
方針：証明済みの充満性・忠実性・本質的全射性をまとめる。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：逆関手と比較の自然同型の構成。 -/
instance toH0_isEquivalence : (toH0 A D).IsEquivalence where

/-- 概要：dg nerve のホモトピー圏は既存の dg 圏の H⁰ と同値。
方針：比較関手の充満・忠実・本質的全射性から Mathlib の圏同値の構成を使う。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：導来 ∞ 圏の通常のホモトピー圏の同定。 -/
def equivalence : nerveHomotopyCategory A D ≌ HomotopyCategory A D :=
  (toH0 A D).asEquivalence

/-- 概要：H⁰ から dg nerve のホモトピー圏への逆関手。
方針：証明済みの比較の圏同値の逆関手を取り出す。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：両向きのホモトピー圏の比較。 -/
def fromH0 : HomotopyCategory A D ⥤ nerveHomotopyCategory A D := (equivalence A D).inverse

/-- 概要：H⁰ を往復する比較は恒等関手に自然同型。
方針：圏同値の余単位の自然同型を用いる。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：両向きの比較が互いに逆であることの確認。 -/
def counitIso : fromH0 A D ⋙ toH0 A D ≅ 𝟭 (HomotopyCategory A D) :=
  (equivalence A D).counitIso

/-- 概要：dg nerve のホモトピー圏を往復する比較は恒等関手に自然同型。
方針：圏同値の単位の自然同型を用いる。
規約：Kerodon §2.5.3（Tag 00PK）。使われ方：両向きの比較が互いに逆であることの確認。 -/
def unitIso : 𝟭 (nerveHomotopyCategory A D) ≅ toH0 A D ⋙ fromH0 A D :=
  (equivalence A D).unitIso

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.11" (partial := component) "仮定：dg 圏（HA と一致。Lean は任意の可換環を許す）。結論：dg nerve の二切断のホモトピー圏と dg 圏の H⁰ 圏の圏同値。比較関手は閉じた辺の境界商を対応させるが、型は通常圏の厳密な同型を与えない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence
attribute [cite HA "1.3.2.2" (partial := special) "仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence
