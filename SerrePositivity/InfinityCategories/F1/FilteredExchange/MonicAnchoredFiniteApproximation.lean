module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.AnchorCylinderKanCorrection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.AnchoredFiniteFactorization
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteAnchorCylinder
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteSubcomplexes

/-!
概要：連続 Kan 模型への有限相対射を、単射な境界を持つ有限模型で近似する。
方針：元の有限因子分解の境界を有限写像円柱で単射にし、境界固定の円柱で補正する。
規約：境界は厳密に保持し、元の全体射への比較は境界上で定値な実ホモトピー。
使われ方：標的 Kan 引き戻しの指定 path を相対持ち上げへ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限相対射は単射な新境界を持つ有限模型を通り、元の境界を全円柱で固定して比較できる。
方針：境界付き有限因子分解に通常の有限写像円柱の補正を適用する。
規約：元の境界から全形状への i の単射性だけを要求。使われ方：指定 path の相対有限検出。 -/
lemma continuousKanReplacement_monic_anchored_finite_approximation {A K E : SSet.{u}}
    [A.Finite] [K.Finite] (i : A ⟶ K) [Mono i] (a : A ⟶ E)
    (f : K ⟶ continuousKanReplacement.obj E)
    (h : a ≫ continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ (M : SSet.{u}) (m : A ⟶ M) (q : M ⟶ E)
      (v : K ⟶ continuousKanReplacement.obj M),
      M.Finite ∧ Mono m ∧ m ≫ q = a ∧
      i ≫ v = m ≫ continuousKanReplacementUnit.app M ∧
      ∃ H : SSet.Homotopy f (v ≫ continuousKanReplacement.map q),
        (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          fst A (Δ[1] : SSet.{u}) ≫ a ≫ continuousKanReplacementUnit.app E := by
  obtain ⟨L, c, r, hc, hr, hf⟩ :=
    continuousKanReplacement_anchored_finite_factorization i a f h
  obtain ⟨v, hv, H, hH⟩ := anchorCylinder_kan_correction i c r hr
  let q := anchorCylinderOut c ≫ L.val.ι
  have hm : anchorCylinderIn c ≫ q = a := by
    dsimp only [q]
    rw [← Category.assoc, anchorCylinderIn_out, hc]
  let H' : SSet.Homotopy f (v ≫ continuousKanReplacement.map q) := {
    h := H.h ≫ continuousKanReplacement.map L.val.ι
    h₀ := by
      change SSet.ι₀ ≫ (H.h ≫ continuousKanReplacement.map L.val.ι) = f
      rw [← Category.assoc, H.h₀, hf]
    h₁ := by
      change SSet.ι₁ ≫ (H.h ≫ continuousKanReplacement.map L.val.ι) =
        v ≫ continuousKanReplacement.map q
      rw [← Category.assoc, H.h₁, Category.assoc, ← CategoryTheory.Functor.map_comp]
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  refine ⟨anchorCylinder c, anchorCylinderIn c, q, v, inferInstance, inferInstance, hm, hv, H', ?_⟩
  change (i ▷ (Δ[1] : SSet.{u})) ≫ (H.h ≫ continuousKanReplacement.map L.val.ι) = _
  have hn : continuousKanReplacementUnit.app L.val ≫ continuousKanReplacement.map L.val.ι =
      L.val.ι ≫ continuousKanReplacementUnit.app E :=
    (continuousKanReplacementUnit.naturality L.val.ι).symm
  rw [← Category.assoc, hH]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc c L.val.ι (continuousKanReplacementUnit.app E), hc]

end SerrePositivity.InfinityCategories.F2
