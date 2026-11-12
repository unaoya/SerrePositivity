module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：h Fun の後合成の充満忠実性を QCat 双圏の Hom 圏へ移す。
方針：二胞体の表示全単射と右 whisker の比較を使う。
規約：対象ごとの hX の充満忠実性だけからは推論しない。
使われ方：B2 の双圏随伴の余単位の可逆性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
local instance postcompHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：h Fun の後合成が充満忠実なら QCat の Hom 圏の後合成も充満忠実。
方針：h Fun の Hom 全単射を二胞体の表示全単射で移す。
規約：パラメータ A は quasicategory。
使われ方：包含の関手 ∞ 圏での充満忠実性から双圏の余単位を可逆にする。 -/
def qcatPostcompFullyFaithfulOfHo (A X Y : SSet.{u})
    [Quasicategory A] [Quasicategory X] [Quasicategory Y] (G : X ⟶ Y)
    (h : (hoFunctor.map ((ihom A).map G)).toFunctor.FullyFaithful) :
    (Bicategory.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).FullyFaithful := by
  have hb (U V : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) : Function.Bijective
      ((Bicategory.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).map :
        (U ⟶ V) → ((U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) ⟶ (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G))) := by
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U.hom V.hom).trans
      (h.homEquiv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U.hom ≫ G) (V.hom ≫ G)).symm)
    have he (α : U ⟶ V) : e α = α ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U.hom ≫ G) (V.hom ≫ G)).injective
      change (hoFunctor.map ((ihom A).map G)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α) = _
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight α G).symm
    constructor
    · intro α β hαβ
      apply e.injective
      rw [he, he]
      exact hαβ
    · intro β
      obtain ⟨α, hα⟩ := e.surjective β
      exact ⟨α, (he α).symm.trans hα⟩
  letI : (Bicategory.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).Full := ⟨fun {U V} => (hb U V).2⟩
  letI : (Bicategory.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).Faithful := ⟨fun {U V} => (hb U V).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
