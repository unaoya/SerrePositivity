module

public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus
public import SerrePositivity.KST.Spectra.ParameterizedExchangeSign
public import SerrePositivity.KST.Spectra.LoopSignComponents

/-!
概要：元の二重 loop 空間そのものの交換符号と二回の符号反転を、普遍的な区間族で実現する。
方針：恒等族に既存の成分の等式を適用して区間を一度選び、全パラメータへ前合成する。
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

/-- 元の同じ Kan 円による二重 loop 空間。 -/
abbrev doubleLoop (Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.basedHom CirclePower.space.{u} (PointedObject.basedHom CirclePower.space.{u} Y)

/-- 元の二つの Kan 円の交換射。 -/
def swap (Y : PointedSimplicialSet.{u}) : doubleLoop Y ⟶ doubleLoop Y :=
  (InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom

/-- 元の内側の Kan 円の符号反転。 -/
def reversal (Y : PointedSimplicialSet.{u}) : doubleLoop Y ⟶ doubleLoop Y :=
  PointedObject.basedHomMap CirclePower.space.{u}
    (Y := PointedObject.basedHom CirclePower.space.{u} Y)
    (Z := PointedObject.basedHom CirclePower.space.{u} Y)
    (PointedMapping.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y)

/-- 二重 loop 空間全体で一度選んだ、交換と符号反転の基点固定区間族。 -/
def exchange {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : KanPiIsomorphism a.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y)) (swap Y) (reversal Y) := by
  have h := omega_exchange_sign_component a ha (𝟙 (doubleLoop Y))
  simp only [Category.id_comp] at h
  exact PointedMapping.basedPathOfComponent h

/-- 二重 loop 空間全体で一度選んだ、二度の符号反転を恒等射へ戻す区間族。 -/
def reversalTwice (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (reversal Y ≫ reversal Y) (𝟙 (doubleLoop Y)) := by
  have h := PointedMapping.componentOf_nested_neg_one_twice (𝟙 (doubleLoop Y))
  simp only [Category.id_comp] at h
  exact PointedMapping.basedPathOfComponent h

/-- 元の交換符号の区間の後で、同じ内側の符号をもう一度反転する。 -/
def cancellationFirst {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : KanPiIsomorphism a.right) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (swap Y ≫ reversal Y) (reversal Y ≫ reversal Y) := (exchange a ha).basedPost (reversal Y)

/-- 元の交換と符号反転を、二つの普遍的な基点固定区間で恒等射へ戻す。 -/
lemma cancellationChain {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : KanPiIsomorphism a.right) :
    PointedMapping.VerticalChain (PointedObject.toPoint (doubleLoop Y))
      (swap Y ≫ reversal Y) (𝟙 (doubleLoop Y)) :=
  (Relation.ReflTransGen.single ⟨cancellationFirst a ha⟩).trans
    (Relation.ReflTransGen.single ⟨reversalTwice Y⟩)

/-- 任意のパラメータ族の交換比較に、元の同じ普遍区間を使う。 -/
def exchangeAt {A Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : KanPiIsomorphism a.right) (f : A ⟶ doubleLoop Y) :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Y))
      (f ≫ swap Y) (f ≫ reversal Y) := (exchange a ha).pre f

/-- 元の部分パラメータへの制限は、選んだ交換比較の区間全体と厳密に可換。 -/
lemma exchangeAt_restriction {A B Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : KanPiIsomorphism a.right) (f : A ⟶ doubleLoop Y) (j : B ⟶ A) :
    (exchangeAt a ha (j ≫ f)).homotopy.h =
      j.right ▷ (Δ[1] : SSet.{u}) ≫ (exchangeAt a ha f).homotopy.h := by
  simp only [exchangeAt, PointedMapping.VerticalPath.pre_homotopy_h,
    Under.comp_right, comp_whiskerRight, Category.assoc]

end SerrePositivity.KST.Spectra.LoopExchangePaths
