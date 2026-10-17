module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison

/-! # 全導来bimodule合成の五角図式の両経路

## 概要
全導来bimodule合成の五角図式の両経路。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonInner.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
  (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
  (S : DerivedBimoduleCategory A F G)

def derivedBimodulePentagonShort :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
      (derivedBimoduleAssociator A B E F G hF hG R S).hom ≫
    (derivedBimoduleAssociator A B C E G hE hG Q
      (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).hom

def derivedBimodulePentagonLong :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerRight (derivedBimoduleAssociator A B C E F hE hF Q R).hom
      ((derivedBimoduleComposeFunctor A B F G hG).obj S) ≫
    (derivedBimoduleAssociator A B C F G hF hG
      (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) S).hom ≫
    (derivedBimoduleComposeFunctor A B C G hG).map
      ((derivedBimoduleAssociator A C E F G hF hG R S).hom.app Q)

end SerrePositivity.DifferentialGraded.BimoduleTensor
