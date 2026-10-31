module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorComparison
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorUnit
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorAssociator
public import Mathlib.Data.ZMod.Basic

/-! # 導来合成関手の比較・右単位・結合自然同型の受入監査

## 概要
導来合成関手の比較・右単位・結合自然同型の受入監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
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
  [Small.{u} B] [Small.{u} C]
variable {Q Q' : BimoduleCategory A C E}

example
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    derivedComposeWith A B C E Q hF ≅ derivedComposeWith A B C E Q' hF' :=
  derivedComposeWithProjectiveIso A B C E hF hF' hQ hQ' g hg

example
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q)) :
    derivedComposeWithProjectiveIso A B C E hF hF hQ hQ (𝟙 Q)
      ((BimoduleCategory.quasiIso A C E).id_mem Q) = Iso.refl _ :=
  derivedComposeWithProjectiveIso_id A B C E hF hQ

example {Q'' : BimoduleCategory A C E}
    (hF : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hF' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hF'' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q''))
    (hQ : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q'))
    (hQ'' : ∀ e, moduleHomotopicallyProjective A C ((BimoduleCategory.evaluation A C E e).obj Q''))
    (g : Q ⟶ Q') (h : Q' ⟶ Q'')
    (hg : BimoduleCategory.quasiIso A C E g) (hh : BimoduleCategory.quasiIso A C E h) :
    derivedComposeWithProjectiveIso A B C E hF hF' hQ hQ' g hg ≪≫
      derivedComposeWithProjectiveIso A B C E hF' hF'' hQ' hQ'' h hh =
    derivedComposeWithProjectiveIso A B C E hF hF'' hQ hQ'' (g ≫ h)
      ((BimoduleCategory.quasiIso A C E).comp_mem g h hg hh) :=
  derivedComposeWithProjectiveIso_trans A B C E hF hF' hF'' hQ hQ' hQ'' g h hg hh

example : derivedComposeWith A B C C
    (BimoduleCategory.of A C C (Bimodule.diagonal A C))
    (Bimodule.diagonal_rightRelativeKFlat A C) ≅ 𝟭 (DerivedBimoduleCategory A B C) :=
  derivedRightUnitIso A B C

variable [Small.{u} E]
-- Fのsmall性を仮定しない実際の導来圏上の結合比較。
example (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R)) :
    derivedComposeWith A B C E Q hQ ⋙ derivedComposeWith A B E F R hR ≅
      derivedComposeWith A B C F
        (BimoduleCategory.of A C F (compose A C E F
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R)))
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R) hQ hR) :=
  derivedAssociatorIso A B C E F Q R hQ hR

example : derivedComposeWith (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
    (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} (Bimodule.diagonal (ZMod 2) PUnit.{1}))
    (Bimodule.diagonal_rightRelativeKFlat (ZMod 2) PUnit.{1}) ≅
    𝟭 (DerivedBimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1}) :=
  derivedRightUnitIso (ZMod 2) PUnit.{1} PUnit.{1}

#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithProjectiveIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithProjectiveIso_hom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithProjectiveIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithProjectiveIso_hom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithProjectiveIso_id
#print axioms
      SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithProjectiveIso_trans
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitLocalizedIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitLocalizedIso_hom_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedRightUnitIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedRightUnitIso_hom_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithAssociatorIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithAssociatorIso_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithPair_fac
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithPair_lifting
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedAssociatorIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedAssociatorIso_hom_app
