module

public import SerrePositivity.InfinityCategories.F2.ContinuousKanRelativeReflection
public import SerrePositivity.InfinityCategories.F2.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.F2.RelativeHomotopyZigzag

/-!
概要：境界付き模型の輸送と Kan fiber への反映を元の境界円柱のまま合成する。
方針：指定輸送の延長・相対反映・境界固定 zigzag の合成。
規約：有限性は仮定しない。使われ方：標的二入力の共通境界付き比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：模型を元の Kan 値へ反映し、比較の境界を指定輸送の像と厳密に一致させる。
方針：指定円柱の延長と相対反映を境界固定で合成。
規約：元の包含 k を保つ。使われ方：二入力を境界円柱とともに元の値へ戻す。 -/
lemma continuousKanReplacement_relative_model_comparison {K M X Y : SSet.{u}}
    [KanComplex Y] (A : K.Subcomplex) (k : Y ⟶ X)
    (a : (A : SSet.{u}) ⟶ X) (t : (A : SSet.{u}) ⟶ Y)
    (m : (A : SSet.{u}) ⟶ M) (q : M ⟶ X) (w : M ⟶ Y) (hw : m ≫ w = t)
    (L : SSet.Homotopy a (t ≫ k)) (G : SSet.Homotopy q (w ≫ k))
    (hG : (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h)
    (z : K ⟶ continuousKanReplacement.obj M)
    (hz : A.ι ≫ z = m ≫ continuousKanReplacementUnit.app M)
    (r₀ : K ⟶ continuousKanReplacement.obj X)
    (U : SSet.Homotopy r₀ (z ≫ continuousKanReplacement.map q))
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ z ≫ continuousKanReplacement.map q) :
    ∃ r : K ⟶ Y, A.ι ≫ r = t ∧
      ∃ T : SSet.Homotopy r₀ (r ≫ k ≫ continuousKanReplacementUnit.app X),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = L.h ≫ continuousKanReplacementUnit.app X := by
  obtain ⟨V, hV⟩ := continuousKanReplacement_specified_homotopy_precomp G A.ι m z hz
  have hz' : A.ι ≫ (z ≫ continuousKanReplacement.map w) =
      t ≫ continuousKanReplacementUnit.app Y := by
    rw [← Category.assoc, hz, Category.assoc, ← continuousKanReplacementUnit.naturality,
      Functor.id_map, ← Category.assoc, hw]
  obtain ⟨r, hr, R, hR⟩ := continuousKanReplacement_relative_reflection
    A.ι t (z ≫ continuousKanReplacement.map w) hz'
  let W : SSet.Homotopy (r ≫ k ≫ continuousKanReplacementUnit.app X)
      (z ≫ continuousKanReplacement.map (w ≫ k)) :=
    { h := R.h ≫ continuousKanReplacement.map k
      h₀ := by
        change SSet.ι₀ ≫ R.h ≫ continuousKanReplacement.map k =
          r ≫ k ≫ continuousKanReplacementUnit.app X
        rw [← Category.assoc, R.h₀, Category.assoc,
          ← continuousKanReplacementUnit.naturality, Functor.id_map]
      h₁ := by
        change SSet.ι₁ ≫ R.h ≫ continuousKanReplacement.map k =
          z ≫ continuousKanReplacement.map (w ≫ k)
        rw [← Category.assoc, R.h₁, Category.assoc, ← Functor.map_comp]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hW : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ W.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ r ≫ k ≫
        continuousKanReplacementUnit.app X := by
    change (A.ι ▷ (Δ[1] : SSet.{u})) ≫ R.h ≫ continuousKanReplacement.map k = _
    rw [← Category.assoc, hR, Category.assoc, Category.assoc,
      ← continuousKanReplacementUnit.naturality, Functor.id_map, ← hr]
    simp only [Category.assoc]
  obtain ⟨T, hT⟩ := exists_relativeHomotopyZigzag A U V W hU hW
  refine ⟨r, hr, T, ?_⟩
  rw [hT, hV, ← Category.assoc, hG]

end SerrePositivity.InfinityCategories.F2
