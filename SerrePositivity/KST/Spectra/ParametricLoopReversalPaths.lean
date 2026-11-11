module

public import SerrePositivity.KST.Spectra.UniversalLoopExchangePaths
public import SerrePositivity.KST.Spectra.DoubleLoopParametricAction
public import SerrePositivity.KST.Spectra.PointedIntervalStrictConjugation
public import SerrePositivity.KST.Spectra.PointedIntervalCotensorConjugation

/-!
概要：現在の同じ二重反転区間は、標準の二重 loop 全族作用に対して実辺全体で自然。
方針：円の同じ区間の前合成像を交換同型で共役し、源の全族自然性を移す。
規約：区間の選択や全族自然性の仮定を追加しない。使われ方：随伴比較の第二辺。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 二重反転の同じ実辺は、円区間の前合成像を交換同型で共役した辺。 -/
lemma reversalTwice_conjugate_path (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (reversalTwice Z).path =
      (((CirclePower.reversalTwicePath.{u}.basedPre
        (PointedObject.basedHom CirclePower.space.{u} Z)).basedPost
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z).hom).pre
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z).inv).path := by
  change (CirclePower.nestedReversalTwicePath Z).path = _
  rw [CirclePower.nestedReversalTwicePath_path]
  have he := PointedMapping.VerticalPath.basedIhomMap_path_congr
    (CirclePower.reversalTwicePre Z) (CirclePower.reversalTwicePath.{u}.basedPre Z)
    CirclePower.space.{u} (CirclePower.reversalTwicePre_path Z)
  exact he.trans (CirclePower.reversalTwicePath.{u}.basedPre_ihom_conjugate_path
    CirclePower.space.{u} Z).symm

/-- 全パラメータ内部 Hom 像も、同じ交換同型の内部 Hom 像による共役と一致する。 -/
lemma reversalTwice_ihom_conjugate_path (P Z : PointedSimplicialSet.{u})
    [KanComplex Z.right] :
    ((reversalTwice Z).basedIhomMap P).path =
      ((((CirclePower.reversalTwicePath.{u}.basedPre
        (PointedObject.basedHom CirclePower.space.{u} Z)).basedIhomMap P).basedPost
          (PointedObject.basedHomMap P
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z).hom)).pre
          (PointedObject.basedHomMap P
            (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z).inv)).path := by
  let O := CirclePower.reversalTwicePath.{u}.basedPre
    (PointedObject.basedHom CirclePower.space.{u} Z)
  let e := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z
  have he := PointedMapping.VerticalPath.basedIhomMap_path_congr
    (reversalTwice Z) ((O.basedPost e.hom).pre e.inv) P (reversalTwice_conjugate_path Z)
  exact he.trans (O.basedIhomMap_conjugate_path P e)

/-- 現在の同じ二重反転辺は、標準の二重 loop 全族後合成と厳密に自然。 -/
lemma reversalTwice_parametric {P Z Z' : PointedSimplicialSet.{u}}
    [KanComplex Z.right] [KanComplex Z'.right] (v : P ⟶ PointedObject.basedHom Z Z') :
    ((reversalTwice Z).basedPost (doubleParametricPost v)).path =
      (((reversalTwice Z').basedIhomMap P).pre (doubleParametricPost v)).path := by
  let O := CirclePower.reversalTwicePath.{u}.basedPre
    (PointedObject.basedHom CirclePower.space.{u} Z)
  let O' := CirclePower.reversalTwicePath.{u}.basedPre
    (PointedObject.basedHom CirclePower.space.{u} Z')
  let e := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z
  let e' := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Z'
  have hn := CirclePower.reversalTwicePath.{u}.basedPre_parametricPost_path
    (v ≫ PointedMapping.ihomAction CirclePower.space.{u} Z Z')
  have he := PointedMapping.VerticalPath.conjugate_natural_path O (O'.basedIhomMap P)
    (doubleParametricPost v) e (PointedMapping.cotensorIso P e')
    (doubleParametricPost v) (swap_doubleParametricPost v) hn
  change (reversalTwice Z).path ≫
      (PointedObject.basedHomMap (doubleLoop Z) (doubleParametricPost v)).right =
    ((reversalTwice Z').basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (doubleParametricPost v)
        (PointedObject.basedHom P (doubleLoop Z'))).right
  rw [reversalTwice_conjugate_path Z, reversalTwice_ihom_conjugate_path P Z']
  exact he

end SerrePositivity.KST.Spectra.LoopExchangePaths
