module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransWhiskering
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompPointwiseInvertible

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
    qcatMap (nerveMap F) ⟶ qcatMap (nerveMap G) :=
  (qcatCellEquiv _ _).symm (F1B.nerveNatTransHom η)

/-- 通常の自然変換の前合成は、対応する二胞体の前合成。 -/
lemma qcatNerveNatTrans_whiskerLeft (H : K ⥤ I) (η : F ⟶ G) :
    qcatNerveNatTrans (Functor.whiskerLeft H η) =
      qcatMap (nerveMap H) ◁ qcatNerveNatTrans η := by
  apply (qcatCellEquiv (nerveMap H ≫ nerveMap F) (nerveMap H ≫ nerveMap G)).injective
  have h := qcatCell_whiskerLeft (nerveMap H) (qcatNerveNatTrans η)
  have ht := F1B.nerveNatTransHom_whiskerLeft H η
  change F1B.nerveNatTransHom (Functor.whiskerLeft H η) =
    (qcatCellEquiv (nerveMap H ≫ nerveMap F) (nerveMap H ≫ nerveMap G))
      (qcatMap (nerveMap H) ◁ qcatNerveNatTrans η)
  exact ht.symm.trans h.symm

/-- 全成分を反転する後合成の下では、同じ比較二胞体が可逆。 -/
lemma qcatNerveNatTrans_whiskerRight_isIso (η : F ⟶ G)
    {Y : SSet.{u}} [Quasicategory Y] (Q : nerve J ⟶ Y)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map Q).toTruncated) :
    IsIso (qcatNerveNatTrans η ▷ qcatMap Q) := by
  have : (qcatHomFunctor (nerve I) Y).Full :=
    ⟨fun k => ⟨CatEnrichedOrdinary.Hom.mk k, rfl⟩⟩
  suffices hi : IsIso ((qcatHomFunctor (nerve I) Y).map (qcatNerveNatTrans η ▷ qcatMap Q)) from
    isIso_of_reflects_iso _ (qcatHomFunctor (nerve I) Y)
  change IsIso (qcatCellEquiv _ _ (qcatNerveNatTrans η ▷ qcatMap Q))
  rw [qcatCell_whiskerRight]
  change IsIso (functorHomPostcomp _ _ Q (F1B.nerveNatTransHom η))
  rw [← F1B.nerveNatTransHomotopy_hom]
  apply functorHomPostcomp_homotopy_isIso_of_pointwise
  intro x
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective x
  exact (isInvertibleEdge_congr
    (e := ((simplicialHomotopyVertexEdge (F1B.nerveNatTransHomotopy η)
      (nerveVertex i)).toTruncated.map ((truncation 2).map Q)))
    (f := ((nerve.edgeMk (η.app i)).map Q).toTruncated)
    (congrArg (Q.app (Opposite.op ⦋1⦌)) (F1B.nerveNatTransHomotopy_component η i))).mpr (hη i)

end SerrePositivity.EInfinity
