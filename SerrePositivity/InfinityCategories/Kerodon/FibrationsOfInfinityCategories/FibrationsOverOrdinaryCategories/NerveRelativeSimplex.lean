module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：底の射列を指定した weighted nerve の単体の重み付き図式。
方針：底の射列の等式で自然変換の標的を同定し、同定と単体の制限の整合性を示す。
規約：等式による同定は射列の表示の変更だけに用いる。
使われ方：Kerodon §5.3.3（Tag 025W）、相対ホーンの各面の係数図式を共通の底に合わせる処理。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の射列が σ と等しい単体から、σ 上の重み付き図式を回収する。
方針：射列の等式に沿って自然変換の標的を同定する。
規約：底の等式 h の証明の選択には依存しない。
使われ方：Kerodon §5.3.3（Tag 025W）、相対ホーンの面の正規化。 -/
def weightedNerveSimplexDiagram {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) (h : s.1 = σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ F := h ▸ s.2

/-- 概要：既に底が σ と表示される単体の重み付き図式は元の自然変換。
方針：反射的な等式による同定を計算する。
規約：任意の τ を扱う。
使われ方：Kerodon §5.3.3（Tag 025W）、相対単体の図式の回収の計算。 -/
lemma weightedNerveSimplexDiagram_mk {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ F) :
    weightedNerveSimplexDiagram F σ ⟨σ, τ⟩ rfl = τ := rfl

/-- 概要：指定した底の上の図式を取り出して単体を組み直すと元に戻る。
方針：単体の依存対を分解して底の等式を消去する。
規約：単体の表示だけを変え、単体自体を変更しない。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーンの既存の面と正規化した面の比較。 -/
lemma weightedNerveSimplexDiagram_eta {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {n : ℕ} (σ : ComposableArrows C n) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) (h : s.1 = σ) :
    (⟨σ, weightedNerveSimplexDiagram F σ s h⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) = s := by
  rcases s with ⟨σ', τ⟩
  cases h
  rfl

/-- 概要：底を指定した図式の回収は単体の制限と可換。
方針：底の等式を消去した後、重みの制限の定義を計算する。
規約：α は任意の単調写像。
使われ方：Kerodon §5.3.3（Tag 025W）、正規化したホーン面の交わりの整合性。 -/
lemma weightedNerveSimplexDiagram_map {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u})
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n.len) (h : s.1 = σ) :
    weightedNerveSimplexDiagram F ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F α s)
        (congrArg (fun q ↦ (SimplexCategory.toCat.map α).toFunctor ⋙ q) h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫
        CategoryTheory.Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
          (weightedNerveSimplexDiagram F σ s h) := by
  rcases s with ⟨σ', τ⟩
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
