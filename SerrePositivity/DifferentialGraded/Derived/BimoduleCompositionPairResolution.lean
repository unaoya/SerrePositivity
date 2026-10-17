module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution
public import SerrePositivity.DifferentialGraded.Derived.RightKFlatComposition

/-! # 全導来合成の二因子を指定K-flat解像度で計算する比較

## 概要
全導来合成の二因子を指定K-flat解像度で計算する比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorResolution.lean、
Derived/BimoduleCompositionPairNaturality.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 二つの全導来合成関手の逐次適用を、指定解像度での逐次適用へ比較する。 -/
def derivedBimoduleComposePairResolutionIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      derivedComposeWith A B C E S.obj S.property ⋙
        derivedComposeWith A B E F T.obj T.property :=
  Functor.isoWhiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q S q hq)
      ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R)) ≪≫
    Functor.isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
      (derivedBimoduleComposeResolutionComputation A B E F hF R T r hr)

/-- 合成された後因子の値を、二つの指定K-flat解像度の通常合成へ比較する。 -/
def derivedBimoduleComposeInnerResolutionIso (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    ((derivedBimoduleComposeFunctor A C E F hF).obj ((bimoduleToDerived A E F).obj R)).obj
        ((bimoduleToDerived A C E).obj Q) ≅
      (bimoduleToDerived A C F).obj (rightKFlatCompose A C E F S T).obj :=
  (derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).app
      ((bimoduleToDerived A C E).obj Q) ≪≫
    ((derivedComposeWith A C E F T.obj T.property).mapIso
      (bimoduleDerivedIso A C E q hq)).symm

/-- 合成された後因子による全導来関手を、解像度の通常合成による関手へ比較する。 -/
def derivedBimoduleComposeNestedResolutionIso (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) ≅
      derivedComposeWith A B C F (rightKFlatCompose A C E F S T).obj
        (rightKFlatCompose A C E F S T).property :=
  (derivedBimoduleComposeFunctor A B C F hF).mapIso
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr) ≪≫
    derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)

end SerrePositivity.DifferentialGraded.BimoduleTensor
