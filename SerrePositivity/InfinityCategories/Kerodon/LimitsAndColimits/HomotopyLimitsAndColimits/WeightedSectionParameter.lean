module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionRoundtrip

/-!
概要：Bousfield–Kan 重みと weighted nerve の切断の対応のパラメータに関する自然性。
方針：初区間のパラメータを前合成する操作を直積の第二因子の写像に移す。
規約：パラメータ間の射に単射性や同値性は要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の切断模型との単体集合の同型の構成。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {A A' : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：重み付き自然変換のパラメータの前合成は、係数のパラメータの後合成に一致する。
方針：各初区間の直積の第二因子に射を適用する式を使う。
規約：底の射列は変えない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断の族のパラメータ自然性。 -/
lemma weightedNerveCoefficients_parameter (f : A' ⟶ A)
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ A') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ◁ (Functor.const I).map f) ≫ η) σ a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η σ (a ≫ f) := by
  apply NatTrans.ext
  funext i
  let w : (Δ[i.val] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj (σ.obj i) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app i
  let b : (Δ[i.val] : SSet.{u}) ⟶ A' :=
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫ a
  change lift w b ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj (σ.obj i) ◁ f) ≫ η.app (σ.obj i) =
    lift w (b ≫ f) ≫ η.app (σ.obj i)
  rw [← Category.assoc, lift_whiskerLeft]

/-- 概要：重み付き自然変換から作る切断の族はパラメータの前合成と可換である。
方針：全単体で係数のパラメータ自然性と Yoneda の後合成の式を使う。
規約：底の nerve 上の実際の射の等式。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の切断模型の普遍性の自然性。 -/
lemma weightedNerveSectionFromTransform_parameter (f : A' ⟶ A)
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ◁ (Functor.const I).map f) ≫ η) =
      (nerve I ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change (⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients _ σ (SSet.yonedaEquiv.symm a)⟩ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex H n) = ⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η σ
      (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋n⦌) a))⟩
  rw [weightedNerveCoefficients_parameter, SSet.yonedaEquiv_symm_comp]

/-- 概要：end への射に対応する切断の族は、普遍的な切断の族のパラメータの前合成である。
方針：end の uncurry の自然性と切断のパラメータ自然性を合成する。
規約：全単射の順方向の実際の評価式を与える。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の切断模型との同型を作る標準射。 -/
lemma bousfieldKanSectionHomEquiv_apply (H : I ⥤ SSet.{u}) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv H A f).val =
      (nerve I ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f) = _
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ◁ (Functor.const I).map f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H)) := by
    simpa only [Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H))
  rw [he, weightedNerveSectionFromTransform_parameter]
  rfl

/-- 概要：end への射と切断の族の全単射はパラメータの前合成について自然である。
方針：普遍的な評価式とテンソルの合成の保存を使う。
規約：射影の条件の証明を除いた実際の切断の射の等式として述べる。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の表現対象の比較の自然性。 -/
lemma bousfieldKanSectionHomEquiv_parameter (f : A' ⟶ A) (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv H A' (f ≫ g)).val =
      (nerve I ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv H A g).val := by
  rw [bousfieldKanSectionHomEquiv_apply, bousfieldKanSectionHomEquiv_apply,
    whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
