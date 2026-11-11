module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDeformationEnriched
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：coherent な単体を最大の区間 path だけを使う単体へ変形する。
方針：標準単体と区間の各単体に、時刻付き path の豊穣関手を対応させる。
規約：値域の局所 Kan 性は変形の構成には要求しない。
使われ方：Kerodon §5.6（Tag 027M）、Proposition 4.6.7.23（Tag 01LW）、標準単体上の表現の局所比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：coherent な単体の Hom を最大の区間 path で評価する。
方針：恒等の対象写像と時刻一による path の変形を前合成する。
規約：全頂点の対象は元の単体と同じ。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の strict な射列との比較の終点。 -/
def coherentSimplexMaximalization {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) : (SimplicialNerve C) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched (OrderHom.id (α := ULift.{u} (Fin (n + 1))))
    (OrderHom.const _ 1)).comp SSet σ

/-- 概要：coherent な単体の path の変形を標準単体と区間からの実際の射にする。
方針：各単体の対象の順序写像と時刻の順序写像を Hom の変形へ代入する。
規約：標準単体の宇宙は coherent nerve の宇宙に合わせる。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の初期値と最大化の間の比較。 -/
def coherentSimplexDeformationMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    (Δ[n] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C where
  app d := ↾fun ⟨a, t⟩ ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a.down.toOrderHom.uliftMap
      (t.down.toOrderHom.comp
        (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (d.unop.len + 1)) →o _))).comp SSet σ
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched _ _).comp SSet σ =
      ((SimplicialThickening.functor α.unop.toOrderHom.uliftMap).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched _ _)).comp SSet σ
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched_reindex]
    rfl

/-- 概要：path の変形の実際の射は元の単体と最大化した単体を結ぶホモトピー。
方針：時刻零の path の像と、時刻一の添字変換の公式で両端を計算する。
規約：端点の単体は Yoneda による射で表示する。
使われ方：Kerodon §5.6（Tag 027M）、標準単体上の coherent な比較を構成する。 -/
def coherentSimplexDeformation {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    SSet.Homotopy (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (coherentSimplexMaximalization σ)) where
  h := coherentSimplexDeformationMap σ
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a.down.toOrderHom.uliftMap
      (OrderHom.const _ 0)).comp SSet σ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched_zero]
    rfl
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched a.down.toOrderHom.uliftMap
      (OrderHom.const _ 1)).comp SSet σ =
      ((SimplicialThickening.functor a.down.toOrderHom.uliftMap).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched (OrderHom.id (α := ULift.{u} (Fin (n + 1))))
          (OrderHom.const _ 1))).comp SSet σ
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationEnriched_reindex]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
