module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor

/-!
概要：Bousfield–Kan end と weighted nerve の切断空間の同型の係数図式に関する自然性。
方針：係数の後合成を切断の族へ移し、普遍的な評価で同型の可換性を検証する。
規約：任意の単体集合値図式と自然変換を扱う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の錐から得る二つの切断模型の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H H' : I ⥤ SSet.{u}}

/-- 概要：end への射の後合成は重み付き自然変換の後合成に移る。
方針：lift の後合成の自然性と lift と uncurry の逆関係を使う。
規約：重み W とパラメータ A は任意。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の係数図式の比較を end の族へ移す式。 -/
lemma weightedSectionsUncurry_postcomp {W : I ⥤ SSet.{u}}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) (η : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f ≫ η := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H' A).symm.injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W η)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f ≫ η)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_postcomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_uncurry]

/-- 概要：重み付き自然変換の後合成は weighted nerve の係数の後合成に一致する。
方針：各初区間の評価の後の結合則を使う。
規約：パラメータと底の射列は固定する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断の係数に関する自然性。 -/
lemma weightedNerveCoefficients_postcomp
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) (η : H ⟶ H')
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (t ≫ η) σ a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients t σ a ≫ Functor.whiskerLeft σ η := by
  apply NatTrans.ext
  funext i
  exact (Category.assoc _ _ _).symm

/-- 概要：自然変換の後合成から作る切断は元の切断と weighted nerve の係数写像の合成である。
方針：各単体で係数の後合成の公式を使う。
規約：底の nerve は変えない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断の族の図式自然性。 -/
lemma weightedNerveSectionFromTransform_postcomp
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) (η : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform (t ≫ η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change (⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (t ≫ η) σ (SSet.yonedaEquiv.symm a)⟩ :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex H' n) = ⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients t σ
      (SSet.yonedaEquiv.symm a) ≫ Functor.whiskerLeft σ η⟩
  rw [weightedNerveCoefficients_postcomp]

/-- 概要：end への射と切断の族の全単射は係数図式の自然変換について自然である。
方針：uncurry と切断の族を作る操作の二つの後合成公式を使う。
規約：全単射の順方向の実際の切断の射で述べる。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の end と切断模型の図式自然性。 -/
lemma bousfieldKanSectionHomEquiv_postcomp (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) (η : H ⟶ H') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv H' A (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv H A f).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η
  rw [weightedSectionsUncurry_postcomp, weightedNerveSectionFromTransform_postcomp]

/-- 概要：普遍的な weighted nerve の切断の族は係数図式の自然変換と可換。
方針：end への恒等射に全単射の図式自然性を適用する。
規約：実際の全空間の係数写像を使う。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の標準比較の可換図式。 -/
lemma bousfieldKanWeightedNerveEvaluation_naturality (η : H ⟶ H') :
    (nerve I ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η := by
  have he := bousfieldKanSectionHomEquiv_postcomp (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H)) η
  rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv_apply, whiskerLeft_id, Category.id_comp] at he
  exact he

/-- 概要：end と切断空間の標準同型は係数図式の自然変換について自然である。
方針：切断空間の普遍的な族で評価し、end の普遍的な評価の自然性を使う。
規約：追加の Kan 性や同値性の仮定を要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の二つの模型の比較の可換性。 -/
lemma bousfieldKanSectionsMap_naturality (η : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap H' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  simp only [whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsMap_evaluation]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap_evaluation,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsMap_evaluation, bousfieldKanWeightedNerveEvaluation_naturality]

/-- 概要：Bousfield–Kan end と weighted nerve の切断空間の同型は図式全体に自然な同型になる。
方針：各図式の同型と、係数写像に関する可換性を束ねる。
規約：全ての単体集合値図式の通常の関手圏上の自然同型。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の strict な係数図式の変更に対する共通模型。 -/
noncomputable def bousfieldKanSectionsNatIso (I : Type u) [SmallCategory I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFunctor I ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsFunctor (nerve I) :=
  NatIso.ofComponents _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionsIso (fun η => (bousfieldKanSectionsMap_naturality η).symm)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
