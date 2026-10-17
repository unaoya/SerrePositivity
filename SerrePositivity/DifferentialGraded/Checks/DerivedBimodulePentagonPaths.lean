module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonPaths
public import Mathlib.Data.ZMod.Basic

/-! # 導来同型で指定した代表との結合比較と五角図式の経路の監査

## 概要
導来同型で指定した代表との結合比較と五角図式の経路の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t x
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : Q ≅ (bimoduleToDerived A C E).obj S.obj)
    (r : R ≅ (bimoduleToDerived A E F).obj T.obj) :
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeNestedComparisonIso A B C E F hF S T q r).hom =
      (derivedBimoduleComposePairComparisonIso A B C E F hE hF S T q r).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom :=
  derivedBimoduleAssociator_comparison_fac A B C E F hE hF S T q r

-- 二経路の型を同時に確認する。ここでは経路の一致は仮定しない。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : DerivedBimoduleCategory A F G) :
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q)) ×
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q)) :=
  ⟨derivedBimodulePentagonShort A B C E F G hE hF hG Q R S,
    derivedBimodulePentagonLong A B C E F G hE hF hG Q R S⟩

example (B : Type v) (C : Type w) (E : Type z) (F : Type t)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [DGCategory (ZMod 2) E] [DGCategory (ZMod 2) F]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F]
    (hE : localHomKFlat (ZMod 2) E) (hF : localHomKFlat (ZMod 2) F)
    (Q : DerivedBimoduleCategory (ZMod 2) C E) (R : DerivedBimoduleCategory (ZMod 2) E F) :
    (derivedBimoduleComposeFunctor (ZMod 2) B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor (ZMod 2) B E F hF).obj R ≅
      (derivedBimoduleComposeFunctor (ZMod 2) B C F hF).obj
        (((derivedBimoduleComposeFunctor (ZMod 2) C E F hF).obj R).obj Q) :=
  derivedBimoduleAssociator (ZMod 2) B C E F hE hF Q R

#print axioms derivedBimoduleAssociator
#print axioms derivedBimoduleAssociator_naturality
#print axioms derivedBimoduleComposePairComparisonIso
#print axioms derivedBimoduleComposeInnerComparisonIso
#print axioms derivedBimoduleComposeNestedComparisonIso
#print axioms derivedBimoduleAssociator_comparison_fac
#print axioms derivedBimodulePentagonShort
#print axioms derivedBimodulePentagonLong
