module

public import SerrePositivity.KST.DerivedGeometry.AffineExtCartan
public import SerrePositivity.KST.DerivedGeometry.SectionsFromExt

/-!
概要：アフィン準連接層の固定基礎環加群層としての基本開上の正次数 Ext 消滅。
方針：実際の準連接層の Čech 完全性を加法群へ移し、証明済みの Cartan 型判定を適用する。
規約：係数環層の加群圏への導来比較とは区別し、固定環の層圏の結論を述べる。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較の基礎。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : CommRingCat.{u}}

local instance (U : TopologicalSpace.Opens (PrimeSpectrum A)) :
    (sheafModuleSections (R := A) (X := TopCat.of (PrimeSpectrum A)) U).Additive :=
  sheafModuleSections_additive (R := A) (X := TopCat.of (PrimeSpectrum A)) U

/--
概要：準連接層の切断の加法群値 Čech 複体は基本開の有限被覆で正次数に完全。
方針：加法群への忘却と有限 Čech 比較同型により既証の加群値完全性を移す。
規約：元の層の実際の切断と交代面微分を用いる。
使われ方：TT §3、Toën §3.2 の Ext 消滅の判定。
-/
lemma relativeAffineQuasicoherentCechAb_exactAt
    (N : (Spec A).Modules) [N.IsQuasicoherent] {ι : Type u} [Finite ι]
    (a : A) (f : ι → A) (hcover : (⨆ i, basicOpen (f i)) = basicOpen a) (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      ((modulesSpecToSheaf.obj N).obj ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).ExactAt
        (n + 1) := by
  let G := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let e := finiteCechFunctorIso G (fun i => basicOpen (f i)) (modulesSpecToSheaf.obj N).obj
  apply (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mp
  exact (relativeAffineQuasicoherentCech_exactAt N a f hcover n).map G

/--
概要：アフィン準連接層を固定 A 加群層として見たとき、基本開の自由層からの正次数 Ext は零。
方針：全基本開被覆の Čech 完全性と Ext の局所消滅からの強帰納を適用する。
規約：対象は固定 A の加群層圏であり、係数環層の加群圏との比較は後続で行う。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅。
-/
lemma affineQuasicoherent_fixedExt_subsingleton
    (N : (Spec A).Modules) [N.IsQuasicoherent] (n : ℕ) (a : A) :
    Subsingleton (Ext ((freeModuleSheafOnOpen A (TopCat.of (PrimeSpectrum A))).obj
      (basicOpen a)) (modulesSpecToSheaf.obj N) (n + 1)) := by
  apply affineExt_subsingleton_of_cech
  intro ι _ b f hcover m
  exact relativeAffineQuasicoherentCechAb_exactAt N b f hcover m

/--
概要：準連接層を固定 A 加群層として見たとき、各基本開の正次数の右導来切断は零。
方針：証明済みの Ext 消滅を分解による右導来切断の消滅へ移す。
規約：固定 A 加群層圏の右導来関手の主張である。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン層コホモロジー。
-/
lemma affineQuasicoherent_fixedRightDerived_isZero
    (N : (Spec A).Modules) [N.IsQuasicoherent] (n : ℕ) (a : A) :
    IsZero (((sheafModuleSections (R := A) (X := TopCat.of (PrimeSpectrum A))
      (basicOpen a)).rightDerived (n + 1)).obj (modulesSpecToSheaf.obj N)) :=
  rightDerivedSections_isZero_of_ext_subsingleton
    (X := TopCat.of (PrimeSpectrum A)) (modulesSpecToSheaf.obj N) (basicOpen a) n
    (affineQuasicoherent_fixedExt_subsingleton N n a)

end SerrePositivity.KST.DerivedGeometry
