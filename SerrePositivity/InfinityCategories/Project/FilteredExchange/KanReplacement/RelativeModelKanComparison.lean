module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanRelativeReflection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanSpecifiedHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyZigzag

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：模型を元の Kan 値へ反映し、比較の境界を指定輸送の像と厳密に一致させる。
方針：指定円柱の延長と相対反映を境界固定で合成。
規約：元の包含 k を保つ。使われ方：二入力を境界円柱とともに元の値へ戻す。 -/
lemma continuousKanReplacement_relative_model_comparison {K M X Y : SSet.{u}}
    [KanComplex Y] (A : K.Subcomplex) (k : Y ⟶ X)
    (a : (A : SSet.{u}) ⟶ X) (t : (A : SSet.{u}) ⟶ Y)
    (m : (A : SSet.{u}) ⟶ M) (q : M ⟶ X) (w : M ⟶ Y) (hw : m ≫ w = t)
    (L : SSet.Homotopy a (t ≫ k)) (G : SSet.Homotopy q (w ≫ k))
    (hG : (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h)
    (z : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj M)
    (hz : A.ι ≫ z = m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app M)
    (r₀ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X)
    (U : SSet.Homotopy r₀ (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map q))
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map q) :
    ∃ r : K ⟶ Y, A.ι ≫ r = t ∧
      ∃ T : SSet.Homotopy r₀ (r ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = L.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
  obtain ⟨V, hV⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_specified_homotopy_precomp G A.ι m z hz
  have hz' : A.ι ≫ (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map w) =
      t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app Y := by
    rw [← Category.assoc, hz, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality,
      Functor.id_map, ← Category.assoc, hw]
  obtain ⟨r, hr, R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_relative_reflection
    A.ι t (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map w) hz'
  let W : SSet.Homotopy (r ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)
      (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (w ≫ k)) :=
    { h := R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map k
      h₀ := by
        change SSet.ι₀ ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map k =
          r ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X
        rw [← Category.assoc, R.h₀, Category.assoc,
          ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
      h₁ := by
        change SSet.ι₁ ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map k =
          z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (w ≫ k)
        rw [← Category.assoc, R.h₁, Category.assoc, ← Functor.map_comp]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hW : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ W.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ r ≫ k ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X := by
    change (A.ι ▷ (Δ[1] : SSet.{u})) ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map k = _
    rw [← Category.assoc, hR, Category.assoc, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map, ← hr]
    simp only [Category.assoc]
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyZigzag A U V W hU hW
  refine ⟨r, hr, T, ?_⟩
  rw [hT, hV, ← Category.assoc, hG]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
