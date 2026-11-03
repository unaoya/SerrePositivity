module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Coherence
public import Mathlib.Data.ZMod.Basic

/-! # 任意K-flat解像度による全導来結合同型の計算と選択独立性の監査

## 概要
任意K-flat解像度による全導来結合同型の計算と選択独立性の監査。

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
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

-- 持ち上げの構成はlocal HomのK-flat性も標的の射影性も要求しない。
example {M N : BimoduleCategory A B C} (q : N ⟶ M)
    (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleToDerived A B C).map (bimoduleCanonicalResolutionLift A B C q hq) ≫
        (bimoduleToDerived A B C).map q =
      (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C M).π :=
  bimoduleCanonicalResolutionLift_fac A B C q hq

example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q) (r : T.obj ⟶ R) (r' : T'.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r') :
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S' T' q' r' hq' hr').hom :=
  (derivedBimoduleAssociatorBaseIso_resolution A B C E F hE hF Q R S T q r hq hr).symm.trans
    (derivedBimoduleAssociatorBaseIso_resolution A B C E F hE hF Q R S' T' q' r' hq' hr')

example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom :=
  derivedBimoduleAssociatorIso_resolution_app A B C E F hE hF Q R S T q r hq hr

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] {M N : BimoduleCategory (ZMod 2) B C} (q : N ⟶ M)
    (hq : BimoduleCategory.quasiIso (ZMod 2) B C q) :
    (bimoduleToDerived (ZMod 2) B C).map
        (bimoduleCanonicalResolutionLift (ZMod 2) B C q hq) ≫
      (bimoduleToDerived (ZMod 2) B C).map q =
    (bimoduleToDerived (ZMod 2) B C).map
      (bimoduleCanonicalSemifreeResolution (ZMod 2) B C M).π :=
  bimoduleCanonicalResolutionLift_fac (ZMod 2) B C q hq

#print axioms bimoduleCanonicalResolutionSourceLift
#print axioms bimoduleCanonicalResolutionLift
#print axioms bimoduleCanonicalResolutionLift_fac
#print axioms derivedBimoduleAssociatorBaseIso_resolution
#print axioms derivedBimoduleAssociatorIso_resolution_app
#print axioms derivedBimoduleAssociatorIso_resolution_fac
#print axioms derivedBimoduleComposePairResolutionIso_self
#print axioms derivedBimoduleComposeInnerResolutionIso_self
#print axioms derivedBimoduleComposeNestedResolutionIso_self
#print axioms derivedBimoduleAssociatorIso_kFlat_fac
