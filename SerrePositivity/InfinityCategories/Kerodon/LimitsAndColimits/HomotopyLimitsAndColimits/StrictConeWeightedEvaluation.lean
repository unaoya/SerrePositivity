module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanSectionsIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber

/-!
概要：strict な錐の標準比較を weighted nerve の切断の族として全次数で評価する。
方針：重み付き end の curry・uncurry の逆性を使い、各初区間で第二射影を計算する。
規約：比較射そのものを評価し、Kan 性や極限性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の strict な錐との整合性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- 概要：strict な錐の標準比較の weighted nerve での評価は錐の脚から直接作る族。
方針：end と切断の全単射の評価式と重み付き curry の逆性を使う。
規約：重みの変数を忘れる第二射影を明示する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の q_x が指定の錐を表すことの高次の検証。 -/
lemma bousfieldKanConeComparison_weightedNerveEvaluation (c : Cone H) :
    (nerve I ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
        (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]

/-- 概要：strict な錐から作る各初区間の係数はパラメータの制限と錐の脚の合成。
方針：重みの評価とパラメータをまとめる直積から第二射影を取る。
規約：底の射列とパラメータの全次数を扱う。
使われ方：HTT 4.2.4.1 の反転した Hom 係数の明示計算。 -/
lemma weightedNerveCoefficients_cone_app (c : Cone H) {n : ℕ}
    (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ c.pt) (j : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients
      (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) σ a).app j =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
      a ≫ c.π.app (σ.obj j) := by
  change lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫ a) ≫
      (snd _ _ ≫ c.π.app (σ.obj j)) = _
  rw [← Category.assoc, lift_snd, Category.assoc]

/-- 概要：strict な錐の標準比較を切断空間へ写して評価すると脚から作った同じ族になる。
方針：切断空間の標準評価を weighted nerve の普遍評価へ戻す。
規約：任意の strict な錐に適用し、極限錐への制限はない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の切断表示を使う q_x の整合性。 -/
lemma bousfieldKanConeComparison_sections_evaluation (c : Cone H) :
    (nerve I ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
      (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) := by
  rw [whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap_evaluation,
    bousfieldKanConeComparison_weightedNerveEvaluation]

/-- 概要：strict な錐の weighted nerve の族を底の頂点で評価すると元の錐の脚になる。
方針：一定の底の全初区間の係数を比較し、Yoneda の後合成の式を使う。
規約：全てのパラメータの単体で厳密に成立する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の標準比較と各 Hom の標準比較の整合性。 -/
lemma weightedNerveSectionFromCone_constant (c : Cone H) (i : I) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) (𝟙 c.pt) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
      (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) =
    c.π.app i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift H i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients
    (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π)
      ((Functor.const (Fin (n + 1))).obj i) (SSet.yonedaEquiv.symm s)).app j = _
  rw [weightedNerveCoefficients_cone_app]
  change _ = SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫
    SSet.yonedaEquiv.symm ((c.π.app i).app (Opposite.op ⦋n⦌) s)
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
