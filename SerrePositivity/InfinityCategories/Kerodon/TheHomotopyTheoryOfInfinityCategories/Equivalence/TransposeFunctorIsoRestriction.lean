module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TransposeFunctorIsoComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.InternalHomSwapNaturality

/-!
概要：指定関手同型の転置と第一変数制限の両立。
方針：内部Homの交換の厳密な自然性を正規化Hom作用へ送る。
規約：比較同型を選び直さず、元の射自身を比較する。
使われ方：Kerodon §4.5.5（Tag 01F6）の関手空間の制限を使う、
指定したstraightening底変換の合成則の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon
namespace TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：指定Homの第一変数制限の転置は、同じ制限関手による後合成。
方針：交換射の自然性を、元の両端点へ正規化して用いる。
規約：任意の単体集合と射を許す。使われ方：指定底変換の合成の転置。 -/
lemma transposeFunctorHom_precomp {A B I X : SSet.{u}} (q : B ⟶ A)
    {F G : A ⟶ (ihom I).obj X} (α : FunctorHom F G) :
    Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
        (transposeFunctorFamily_comp q F) (transposeFunctorFamily_comp q G)
        (transposeFunctorHom (precomposeFunctorHom q α)) =
      postcomposeFunctorHom ((pre q).app X) (transposeFunctorHom α) := by
  unfold transposeFunctorHom
  rw [kanFunctorHomCongr_normalizedMap]
  unfold precomposeFunctorHom postcomposeFunctorHom
  rw [normalizedVertexHomMap_comp, normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map ((pre q).app ((ihom I).obj X) ≫
        (internalHomSwapIso B I X).hom)).toFunctor.map α)
      ((hoFunctor.map ((internalHomSwapIso A I X).hom ≫
        (ihom I).map ((pre q).app X))).toFunctor.map α) := by
    rw [internalHomSwap_pre_left]
  exact eq_of_heq ((normalizedVertexHomMap_heq _ _ _ α).trans
    (hm.trans (normalizedVertexHomMap_heq _ _ _ α).symm))

/-- 概要：指定同型の第一変数制限は転置後に同じ内部Hom制限への後合成になる。
方針：元のHomの転置の制限公式を使う。規約：全図式の同じ同型を保持する。
使われ方：共同切断の指定底変換の合成を転置する。 -/
lemma functorIsoTranspose_precomp {A B I X : SSet.{u}} (q : B ⟶ A)
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) :
    diagramIsoCongr (transposeFunctorFamily_comp q F) (transposeFunctorFamily_comp q G)
        (e.precomp q).transpose = e.transpose.postcomp ((pre q).app X) := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoTranspose_hom, functorIsoPrecomp_hom,
    functorIsoPostcomp_hom, functorIsoTranspose_hom]
  exact transposeFunctorHom_precomp q e.hom

end TheHomotopyTheoryOfInfinityCategories.Equivalence
end SerrePositivity.InfinityCategories.Kerodon
