module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransWhiskering
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPostcompPointwiseInvertible

/-!
# 通常の自然変換から局所化の比較二胞体へ

## 概要
HA §1.3.4 の導来関手の比較として、元の通常の自然変換の辺を使う。

## 方針
同じ辺を二胞体として前後合成し、成分が反転されれば比較を可逆にする。

## 規約
自然変換の別の代表を選ばない。

## 使われ方
Barratt–Eccles 代数の底変更随伴の比較。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Bicategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

local instance localizedNerveNatTransHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

variable {I J K : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} K]
  {F G : I ⥤ J}

/-- 通常の自然変換を同じ nerve の二胞体として読む。 -/
def qcatNerveNatTrans (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom η)

/-- 通常の自然変換の前合成は、対応する二胞体の前合成。 -/
lemma qcatNerveNatTrans_whiskerLeft (H : K ⥤ I) (η : F ⟶ G) :
    qcatNerveNatTrans (Functor.whiskerLeft H η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap H) ◁ qcatNerveNatTrans η := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (nerveMap H ≫ nerveMap F) (nerveMap H ≫ nerveMap G)).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft (nerveMap H) (qcatNerveNatTrans η)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerLeft H η
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (Functor.whiskerLeft H η) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (nerveMap H ≫ nerveMap F) (nerveMap H ≫ nerveMap G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap (nerveMap H) ◁ qcatNerveNatTrans η)
  exact ht.symm.trans h.symm

/-- 全成分を反転する後合成の下では、同じ比較二胞体が可逆。 -/
lemma qcatNerveNatTrans_whiskerRight_isIso (η : F ⟶ G)
    {Y : SSet.{u}} [Quasicategory Y] (Q : nerve J ⟶ Y)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (η.app i)).map Q).toTruncated) :
    IsIso (qcatNerveNatTrans η ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap Q) := by
  have : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor (nerve I) Y).Full :=
    ⟨fun k => ⟨CatEnrichedOrdinary.Hom.mk k, rfl⟩⟩
  suffices hi : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor (nerve I) Y).map (qcatNerveNatTrans η ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap Q)) from
    isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor (nerve I) Y)
  change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (qcatNerveNatTrans η ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap Q))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight]
  change IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp _ _ Q (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom η))
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_hom]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_homotopy_isIso_of_pointwise
  intro x
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).toTruncated.map ((truncation 2).map Q)))
    (f := ((nerve.edgeMk (η.app i)).map Q).toTruncated)
    (congrArg (Q.app (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component η i))).mpr (hη i)

end SerrePositivity.EInfinity
