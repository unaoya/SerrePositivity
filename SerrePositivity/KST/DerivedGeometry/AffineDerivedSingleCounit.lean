module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlusFullyFaithful
public import SerrePositivity.KST.DerivedGeometry.ExactDerivedPlusSingle

/-!
概要：単一の準連接係数層でアフィン導来余単位は同型。
方針：通常の係数準連接同値と単一複体比較で導来 tilde の実際の像と同型にする。
規約：任意の整数次数。冪等完備化を取らない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の本質的全射性の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：準連接係数層の単一対象はその大域切断の単一対象の導来 tilde と同型。
方針：完全 tilde の単一比較と通常の係数同値の単位の逆を合成する。
規約：全係数層の実際の導来圏での同型。
使われ方：TT §3、Toën §3.2 の冪等完備化を介さない像の構成。
-/
def affineDerivedSingleImageIso
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) (n : ℤ) :
    (affineDerivedTildePlus (R := R) H).obj
      ((DerivedCategory.Plus.singleFunctor _ n).obj ((affineQcohΓ (R := R) H).obj F)) ≅
      (DerivedCategory.Plus.singleFunctor _ n).obj F.obj :=
  exactDerivedPlusSingleIso (affineCoefficientTildeFunctor (R := R) H) n _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ n).mapIso
      ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).qcohInclusion.mapIso
        ((affineCoefficientEquivalence (R := R) H).unitIso.symm.app F))

/--
概要：任意の次数の単一準連接係数層で導来余単位は同型。
方針：完全忠実な導来 tilde の実際の像との同型と随伴の余単位判定を使う。
規約：像を形式的な未証明条件として与えない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の本質的全射性の帰納。
-/
lemma affineDerivedPlus_counit_single_isIso
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh) (n : ℤ) :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).counit.app
      ((DerivedCategory.Plus.singleFunctor _ n).obj F.obj)) :=
  (affineDerivedPlusAdjunction (R := R) H).isIso_counit_app_of_iso
    (affineDerivedSingleImageIso H F n).symm

end SerrePositivity.KST.DerivedGeometry
