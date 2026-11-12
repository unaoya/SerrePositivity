module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の小圏の図式に対する Bousfield–Kan 型の重みと標準比較射。
方針：共変な i ↦ N(I/i) を重みとする単体的自然変換の空間を使う。
規約：この段階では end の構成と比較射だけを公開し、Kan 性と極限性は別に証明する。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、7.5.4.1（Tag 03B6）、7.5.4.6（Tag 03BB） の homotopy 極限の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan の共変な重み i ↦ N(I/i)。
方針：over 圏への後合成関手と nerve 関手を合成する。
規約：I/i の対象は終点 i を持つ射であり、i から出る射ではない。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の切断模型と比較する重み付き end。 -/
@[kerodon 03A0]
def bousfieldKanWeight (I : Type u) [SmallCategory I] : I ⥤ SSet.{u} :=
  Over.mapFunctor I ⋙ nerveFunctor

/-- 概要：Bousfield–Kan 型の end による homotopy 極限の候補。
方針：N(I/i) を重みとする単体的自然変換の空間を取る。
規約：任意の H で定義する。Kan 図式での homotopy 極限性は別の証明対象。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、γ3 の標準比較射の具体的な標的。 -/
@[kerodon 03A0]
noncomputable def bousfieldKanHolim (H : I ⥤ SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (bousfieldKanWeight I) H

/-- 概要：strict な錐から Bousfield–Kan 型の end への標準射。
方針：各重みの変数を忘れ、錐の成分を評価する。
規約：錐が極限錐であることは定義に不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の homotopy 極限錐の比較射。 -/
noncomputable def bousfieldKanConeComparison {H : I ⥤ SSet.{u}} (c : Cone H) :
    c.pt ⟶ bousfieldKanHolim H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (bousfieldKanWeight I) c

/-- 概要：strict な極限から Bousfield–Kan 型の end への標準比較射。
方針：選択された極限錐に錐の比較を適用する。
規約：一般の図式ではこの射が同値だとは主張しない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、fibration の引き戻しや塔で同値性を検証する射。 -/
noncomputable def bousfieldKanLimitComparison (H : I ⥤ SSet.{u}) :
    limit H ⟶ bousfieldKanHolim H :=
  bousfieldKanConeComparison (limit.cone H)

/-- 概要：strict な極限の比較射の成分は極限射影の定値の族。
方針：重み付き切断への持ち上げの成分を計算する。
規約：N(I/i) の全ての単体で同じ極限射影を使う。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の κ と θ の合成の計算。 -/
lemma bousfieldKanLimitComparison_π (H : I ⥤ SSet.{u}) (i : I) :
    bousfieldKanLimitComparison H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (bousfieldKanWeight I) H i =
      curry (snd (nerve (Over i)) (limit H) ≫ limit.π H i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π (bousfieldKanWeight I) (limit.cone H) i

/-- 概要：Bousfield–Kan 型の end の i での評価。
方針：I/i の恒等射の対象に対応する nerve の頂点で切断を評価する。
規約：一般の切断の評価の族を strict な錐だとはみなさない。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の標準比較の成分の回収。 -/
noncomputable def bousfieldKanEvaluation (H : I ⥤ SSet.{u}) (i : I) :
    bousfieldKanHolim H ⟶ H.obj i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsEval (bousfieldKanWeight I) H i
    (ComposableArrows.mk₀ (Over.mk (𝟙 i)))

/-- 概要：strict な極限の比較射を i で評価すると極限射影。
方針：重みの任意の頂点で錐の成分を回収する一般公式を使う。
規約：実際の標準比較射についての厳密な等式。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の κ と元の極限錐の整合性。 -/
lemma bousfieldKanLimitComparison_evaluation (H : I ⥤ SSet.{u}) (i : I) :
    bousfieldKanLimitComparison H ≫ bousfieldKanEvaluation H i = limit.π H i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_eval (bousfieldKanWeight I) (limit.cone H) i _

/-- 概要：Bousfield–Kan 型の構成を図式から単体集合への関手にする。
方針：重みを固定した重み付き切断関手を使う。
規約：任意の単体集合の図式で定義する。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、homotopy 極限模型の図式に関する関手性。 -/
noncomputable def bousfieldKanHolimFunctor (I : Type u) [SmallCategory I] :
    (I ⥤ SSet.{u}) ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsFunctor (bousfieldKanWeight I)

/-- 概要：strict 極限からの標準比較射は図式の自然変換に自然。
方針：重み付き end の全ての成分で、極限射影の自然性と curry の公式を使う。
規約：図式が Kan であることや比較射が同値であることは不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、sHom の図式の比較を自然に移す。 -/
lemma bousfieldKanLimitComparison_naturality {H H' : I ⥤ SSet.{u}} (η : H ⟶ H') :
    bousfieldKanLimitComparison H ≫ (bousfieldKanHolimFunctor I).map η =
      lim.map η ≫ bousfieldKanLimitComparison H' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (bousfieldKanWeight I) (limit.cone H) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _ η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ H' i =
    (lim.map η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (bousfieldKanWeight I) (limit.cone H')) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ _ H' i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_right]
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_left]
  congr 1
  change snd ((bousfieldKanWeight I).obj i) (limit H) ≫ limit.π H i ≫ η.app i =
    ((bousfieldKanWeight I).obj i ◁ lim.map η) ≫
      snd ((bousfieldKanWeight I).obj i) (limit H') ≫ limit.π H' i
  conv_rhs => rw [← Category.assoc, whiskerLeft_snd, Category.assoc, limit.map_π]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
