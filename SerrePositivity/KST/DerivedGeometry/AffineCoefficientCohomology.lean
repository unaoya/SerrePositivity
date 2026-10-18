module

public import SerrePositivity.KST.DerivedGeometry.RingedAffineExtCartan
public import SerrePositivity.KST.DerivedGeometry.RingedSectionsFromExt
public import SerrePositivity.KST.DerivedGeometry.AffineQuasicoherentExt

/-!
概要：アフィンスキーム上の実際の係数加群層圏における準連接層の高次切断消滅。
方針：基礎 O 加群層の Čech 完全性と環層上の自由分解による Ext の強帰納を組み合わせる。
規約：任意の係数環層について、基礎層の準連接性だけを要求する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : CommRingCat.{u}} (B : CoefficientSheaf (Spec A))

local instance (U : TopologicalSpace.Opens (PrimeSpectrum A)) :
    (ringedModuleSections (TopCat.of (PrimeSpectrum A)) B.ring U).Additive :=
  ringedModuleSections_additive (TopCat.of (PrimeSpectrum A)) B.ring U

/--
概要：アフィン準連接係数加群層の基本開からの自由加群層を始域とする正次数 Ext は零。
方針：基礎準連接 O 加群層の Čech 完全性を実際の係数加群層圏の Cartan 型判定へ適用する。
規約：係数の可換性・平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン消滅。
-/
lemma affineCoefficient_ext_subsingleton (F : B.QCoh) (n : ℕ) (a : A) :
    Subsingleton (Ext ((ringedFreeSheafOnOpen (TopCat.of (PrimeSpectrum A)) B.ring).obj
      (basicOpen a)) F.obj (n + 1)) := by
  let : (B.forget.obj F.obj).IsQuasicoherent := F.property
  apply ringedAffineExt_subsingleton_of_cech B.ring
  intro ι _ b f hcover m
  exact relativeAffineQuasicoherentCechAb_exactAt (B.forget.obj F.obj) b f hcover m

/--
概要：アフィン準連接係数加群層の各基本開上の正次数右導来切断は零対象。
方針：元の係数加群層圏で証明した Ext 消滅を実際の injective 分解による切断へ移す。
規約：H_X から固定環への忘却が injective を保つことも H の平坦性も仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/
lemma affineCoefficient_rightDerivedSections_isZero (F : B.QCoh) (n : ℕ) (a : A) :
    IsZero (((ringedModuleSections (TopCat.of (PrimeSpectrum A)) B.ring
      (basicOpen a)).rightDerived (n + 1)).obj F.obj) :=
  ringedRightDerivedSections_isZero_of_ext_subsingleton (TopCat.of (PrimeSpectrum A)) B.ring
    F.obj (basicOpen a) n (affineCoefficient_ext_subsingleton B F n a)

/--
概要：全空間上の自由係数加群層から準連接係数層への正次数 Ext は零。
方針：D(1) の Ext 消滅を全空間へ移す。
規約：実際の係数加群層圏の Ext。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の大域切断。
-/
lemma affineCoefficient_globalExt_subsingleton (F : B.QCoh) (n : ℕ) :
    Subsingleton (Ext ((ringedFreeSheafOnOpen (TopCat.of (PrimeSpectrum A)) B.ring).obj
      ⊤) F.obj (n + 1)) := by
  have hU : basicOpen (1 : A) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum A)) := basicOpen_one
  exact (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum A) =>
    Subsingleton (Ext ((ringedFreeSheafOnOpen (TopCat.of (PrimeSpectrum A)) B.ring).obj U)
      F.obj (n + 1))) hU).mp (affineCoefficient_ext_subsingleton B F n 1)

/--
概要：アフィン準連接係数加群層の正次数右導来大域切断は零対象。
方針：基本開 D(1) の消滅を全空間へ書き換える。
規約：元の係数加群層圏の右導来関手を使う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/
lemma affineCoefficient_globalRightDerivedSections_isZero (F : B.QCoh) (n : ℕ) :
    IsZero (((ringedModuleSections (TopCat.of (PrimeSpectrum A)) B.ring
      ⊤).rightDerived (n + 1)).obj F.obj) := by
  have hU : basicOpen (1 : A) = (⊤ : TopologicalSpace.Opens (PrimeSpectrum A)) := basicOpen_one
  exact (congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum A) =>
    IsZero (((ringedModuleSections (TopCat.of (PrimeSpectrum A)) B.ring U).rightDerived
      (n + 1)).obj F.obj)) hU).mp (affineCoefficient_rightDerivedSections_isZero B F n 1)

/--
概要：左 H 加群の実際のアフィン係数 tilde は各基本開の切断関手について非輪状。
方針：係数 tilde の準連接性と任意の係数環層に対する消滅定理を使う。
規約：H は非可換でもよく、A 上の平坦性は要求しない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の係数 tilde の導来比較。
-/
lemma affineCoefficientTilde_rightDerivedSections_isZero
    (H : Type u) [Ring H] [Algebra A H] (M : ModuleCat.{u} H) (n : ℕ) (a : A) :
    IsZero (((ringedModuleSections (TopCat.of (PrimeSpectrum A))
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso A).inv.hom).ring
        (basicOpen a)).rightDerived (n + 1)).obj ((affineCoefficientTildeFunctor H).obj M)) :=
  affineCoefficient_rightDerivedSections_isZero _
    ((affineCoefficientEquivalence (R := A) H).inverse.obj M) n a

end SerrePositivity.KST.DerivedGeometry
