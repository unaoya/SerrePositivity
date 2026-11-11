module

public import SerrePositivity.KST.Spectra.LoopExchangeOperators

public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus
public import SerrePositivity.KST.Spectra.ParameterizedExchangeSign
public import SerrePositivity.KST.Spectra.LoopSignComponents
public import SerrePositivity.KST.Spectra.NaturalLoopReversalPaths
public import SerrePositivity.KST.Spectra.DeloopedTracedExchange
public import SerrePositivity.KST.Spectra.LoopExchangeFamilyTrace
public import SerrePositivity.KST.Spectra.OrdinaryLoopUniversalNaturality

/-!
概要：元の二重 loop 空間そのものの交換符号と二回の符号反転を、普遍的な区間族で実現する。
方針：通常円を内側にする一つの普遍区間を元の随伴へ移し、全トレースを保持する。
規約：指定部分への垂直性は別条件。使われ方：元の随伴構造比較の区間データの追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 一つの普遍区間から Ω 条件へ移した、交換と符号反転の基点固定区間族。 -/
def exchange {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y)) (swap Y) (reversal Y) :=
  LoopExchangeFamily.exchange OrdinaryLoopSource.family.{u} a ha

/-- 既存の交換区間の辺全体は、同じ写像 path 持ち上げの源射影そのもの。 -/
lemma exchange_path {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    (exchange a ha).path =
      (LoopExchangeFamily.trace OrdinaryLoopSource.family.{u} a ha).path.path := rfl

/-- 円自身の一つの区間から移した、二度の符号反転を恒等射へ戻す自然な区間族。 -/
def reversalTwice (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (reversal Y ≫ reversal Y) (𝟙 (doubleLoop Y)) :=
  CirclePower.nestedReversalTwicePath Y

/-- 同じ二重反転区間は、標的の後合成と辺全体で厳密に可換。 -/
lemma reversalTwice_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (v : Y ⟶ Z) :
    ((reversalTwice Y).basedPost (PointedObject.basedHomMap CirclePower.space.{u}
      (Y := PointedObject.basedHom CirclePower.space.{u} Y)
      (Z := PointedObject.basedHom CirclePower.space.{u} Z)
      (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) v))).path =
    ((reversalTwice Z).pre (PointedObject.basedHomMap CirclePower.space.{u}
      (Y := PointedObject.basedHom CirclePower.space.{u} Y)
      (Z := PointedObject.basedHom CirclePower.space.{u} Z)
      (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) v))).path :=
  CirclePower.nestedReversalTwicePath_natural v

/-- 元の交換符号の区間の後で、同じ内側の符号をもう一度反転する。 -/
def cancellationFirst {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (swap Y ≫ reversal Y) (reversal Y ≫ reversal Y) := (exchange a ha).basedPost (reversal Y)

/-- 元の交換と符号反転を、二つの普遍的な基点固定区間で恒等射へ戻す。 -/
lemma cancellationChain {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    PointedMapping.VerticalChain (PointedObject.toPoint (doubleLoop Y))
      (swap Y ≫ reversal Y) (𝟙 (doubleLoop Y)) :=
  (Relation.ReflTransGen.single ⟨cancellationFirst a ha⟩).trans
    (Relation.ReflTransGen.single ⟨reversalTwice Y⟩)

/-- 任意のパラメータ族の交換比較に、元の同じ普遍区間を使う。 -/
def exchangeAt {A Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) (f : A ⟶ doubleLoop Y) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (f ≫ swap Y) (f ≫ reversal Y) := (exchange a ha).pre f

/-- 元の部分パラメータへの制限は、選んだ交換比較の区間全体と厳密に可換。 -/
lemma exchangeAt_restriction {A B Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) (f : A ⟶ doubleLoop Y) (j : B ⟶ A) :
    (exchangeAt a ha (j ≫ f)).homotopy.h =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ (exchangeAt a ha f).homotopy.h := by
  simp only [exchangeAt, PointedMapping.VerticalPath.pre_homotopy_h,
    Under.comp_right, comp_whiskerRight, Category.assoc]

end SerrePositivity.KST.Spectra.LoopExchangePaths
