module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MaximalPathFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexDeformationIso

/-!
概要：任意の coherent な単体を通常の射列の coherent な表示と比較する。
方針：最大区間 path を元の豊穣関手で写し、最大化の関手同型に接続する。
規約：標準単体上の局所的な strict 化であり、一般の底上の strict 化は主張しない。
使われ方：Kerodon §5.6（Tag 027M）、境界付きの表現の比較に向けた局所モデル。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：coherent な単体から全区間 path に沿う通常の射列を取り出す。
方針：最大区間 path の通常の関手と、元の豊穣関手の通常の作用を合成する。
規約：対象は元の単体の各頂点の対象。
使われ方：Kerodon §5.6（Tag 027M）、標準単体上の coherent な図式の strict な比較先。 -/
def coherentSimplexStrictDiagram {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPathFunctor _ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor σ

/-- 概要：取り出した射列の各対象は元の coherent な単体の対象。
方針：二つの通常の関手の対象写像を展開する。
規約：頂点の番号は Hom の宇宙へ ULift する。
使われ方：Kerodon §5.6（Tag 027M）、局所的な strict 化の対象の整合性。 -/
lemma coherentSimplexStrictDiagram_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (i : Fin (n + 1)) :
    (coherentSimplexStrictDiagram σ).obj (ULift.up i) = σ.obj ⟨ULift.up i⟩ := rfl

/-- 概要：最大化した coherent な単体は取り出した通常の射列の coherent な表示に等しい。
方針：時刻一の変形を最大区間 path の図式に置き換え、豊穣後合成の公式を使う。
規約：頂点だけでなく全ての豊穣 Hom の射の厳密な等式。
使われ方：Kerodon §5.6（Tag 027M）、局所的な strict 化のホモトピーの終点の同定。 -/
lemma coherentSimplexMaximalization_eq_strictDiagram
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization σ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (coherentSimplexStrictDiagram σ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp]
  rfl

/-- 概要：任意の coherent な単体は通常の射列の coherent な表示と関手同型。
方針：点ごとに恒等の変形の関手同型の終点を、通常の射列の表示へ置き換える。
規約：coherent nerve が quasicategory の場合に適用する。
使われ方：Kerodon §5.6（Tag 027M）、空間値または圏値の標準単体上の図式の局所比較。 -/
noncomputable def coherentSimplexStrictificationIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] [Quasicategory (SimplicialNerve C)]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (coherentSimplexStrictDiagram σ))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalizationIso σ
  rw [coherentSimplexMaximalization_eq_strictDiagram] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
