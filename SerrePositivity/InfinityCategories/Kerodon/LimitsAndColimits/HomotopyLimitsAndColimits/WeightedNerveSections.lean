module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedNerveCoefficients

/-!
概要：Bousfield–Kan 重みの自然変換の族から weighted nerve の切断の族を作る。
方針：底の射列ごとに初区間の係数を作り、制限の公式で単体的自然性を確認する。
規約：底を保つ射を構成する段階であり、切断との逆対応は後続。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の weighted nerve の切断模型。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：重み付き自然変換とパラメータから底の nerve 上の weighted nerve の切断の族を作る。
方針：底の単体の全初区間で重み付き自然変換を評価して係数を添える。
規約：パラメータと係数図式の Kan 性は不要。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end から切断の族への比較。 -/
noncomputable def weightedNerveSectionFromTransform
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H where
  app d := ↾fun s => ⟨s.1, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η s.1 (SSet.yonedaEquiv.symm s.2)⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, a⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η ((SimplexCategory.toCat.map α.unop).toFunctor ⋙ σ)
      (SSet.yonedaEquiv.symm (A.map α a)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α.unop ≫ Functor.whiskerLeft
          (SimplexCategory.toCat.map α.unop).toFunctor
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η σ (SSet.yonedaEquiv.symm a))
    have hy : SSet.yonedaEquiv.symm (A.map α a) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm a :=
      (SSet.yonedaEquiv_symm_naturality_left (X := A) α.unop a).symm
    rw [hy]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients_restriction η α.unop σ _

/-- 概要：構成した weighted nerve への射は底でパラメータを忘れる射である。
方針：各次数で底の射列をそのまま使うことを計算する。
規約：底の射影を厳密に保つ。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断空間へ curry する条件。 -/
lemma weightedNerveSectionFromTransform_projection
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    weightedNerveSectionFromTransform η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A := rfl

/-- 概要：Bousfield–Kan 重み付き end の普遍的な weighted nerve の切断の族。
方針：重み付き end の恒等射を uncurry して一般の切断の族の構成へ渡す。
規約：切断との同型性や coherent な錐との比較はこの定義には含まない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の主比較に用いる切断模型への評価。 -/
noncomputable def bousfieldKanWeightedNerveEvaluation (H : I ⥤ SSet.{u}) :
    nerve I ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H :=
  weightedNerveSectionFromTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H)))

/-- 概要：普遍的な weighted nerve の切断の族は底で第一射影に一致する。
方針：一般の自然変換から作った射の射影の公式を使う。
規約：重み付き end の Kan 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の切断空間への標準射の固定条件。 -/
lemma bousfieldKanWeightedNerveEvaluation_projection (H : I ⥤ SSet.{u}) :
    bousfieldKanWeightedNerveEvaluation H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H =
      fst (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
