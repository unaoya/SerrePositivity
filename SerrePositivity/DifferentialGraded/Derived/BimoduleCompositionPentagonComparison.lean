module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonInner

/-! # 全導来五角図式の始域と両終域のK-flat比較

## 概要
全導来五角図式の始域と両終域のK-flat比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagonShort.lean。
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

/-- 短経路の最初の二因子比較と整合する三つの作用関手の比較。 -/
def derivedBimoduleTripleSourceIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R.obj) ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj) ≅
      rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ⋙
        rightKFlatDerivedCompose A B F G S :=
  isoWhiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj
      ((bimoduleToDerived A C E).obj Q.obj))
    (isoWhiskerRight (derivedBimoduleComposeKFlatIso A B E F hF R)
        ((derivedBimoduleComposeFunctor A B F G hG).obj ((bimoduleToDerived A F G).obj S.obj)) ≪≫
      isoWhiskerLeft (rightKFlatDerivedCompose A B E F R)
        (derivedBimoduleComposeKFlatIso A B F G hG S)) ≪≫
    isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q)
      (rightKFlatDerivedCompose A B E F R ⋙ rightKFlatDerivedCompose A B F G S)

def derivedBimoduleTripleLeftFunctorIso (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C F G hG).obj
          ((bimoduleToDerived A F G).obj S.obj)).obj
            (((derivedBimoduleComposeFunctor A C E F hF).obj
              ((bimoduleToDerived A E F).obj R.obj)).obj ((bimoduleToDerived A C E).obj Q.obj))) ≅
      rightKFlatDerivedCompose A B C G
        (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S) :=
  (derivedBimoduleComposeFunctor A B C G hG).mapIso
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S) ≪≫
    derivedBimoduleComposeKFlatIso A B C G hG
      (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)

def derivedBimoduleTripleRightFunctorIso (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj
            ((bimoduleToDerived A F G).obj S.obj)).obj ((bimoduleToDerived A E F).obj R.obj))).obj
              ((bimoduleToDerived A C E).obj Q.obj)) ≅
      rightKFlatDerivedCompose A B C G
        (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S)) :=
  (derivedBimoduleComposeFunctor A B C G hG).mapIso
      (derivedBimoduleTripleRightValueIso A C E F G hG Q R S) ≪≫
    derivedBimoduleComposeKFlatIso A B C G hG
      (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))

/-- 内側の全結合射を作用関手へ送った射の比較square。 -/
lemma derivedBimoduleTripleFunctorIso_associator (hF : localHomKFlat A F)
    (hG : localHomKFlat A G) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleComposeFunctor A B C G hG).map
        ((derivedBimoduleAssociator A C E F G hF hG
          ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
            ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleTripleRightFunctorIso A B C E F G hG Q R S).hom =
    (derivedBimoduleTripleLeftFunctorIso A B C E F G hF hG Q R S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom := by
  have hv := derivedBimoduleTripleValueIso_associator A C E F G hF hG Q R S
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C G hG
    (show rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S ⟶
      rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S) from
        ⟨(associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj)
          (BimoduleCategory.underlying A F G S.obj)).hom⟩)
  change _ ≫ ((derivedBimoduleComposeFunctor A B C G hG).map
      (derivedBimoduleTripleRightValueIso A C E F G hG Q R S).hom ≫ _) =
    ((derivedBimoduleComposeFunctor A B C G hG).map
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S).hom ≫ _) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hv,
    CategoryTheory.Functor.map_comp, Category.assoc, hk, ← Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
