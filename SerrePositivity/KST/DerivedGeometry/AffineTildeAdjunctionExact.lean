module

public import SerrePositivity.KST.DerivedGeometry.AffineTildeAdjunction
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeExact
public import SerrePositivity.KST.DerivedGeometry.AffineGammaAcyclic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
概要：アフィン tilde 随伴の単位同型と大域切断の injective 保存。
方針：構成した Hom 同値で単位を計算し、完全な左随伴による injective 保存を適用する。
規約：全係数加群層を扱い、H の平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数導来随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：全係数加群層へのアフィン tilde 随伴の単位は自然同型。
方針：単位の各成分を係数同値の余単位の逆と恒等射の大域切断に計算する。
規約：準連接層圏の同値だけで全導来圏の同値とは結論しない。
使われ方：TT §3、Toën §3.2 のアフィン導来単位。
-/
instance affineCoefficientTildeAdjunction_unit_isIso :
    IsIso (affineCoefficientTildeAdjunction (R := R) H).unit := by
  have (M : ModuleCat.{u} H) : IsIso ((affineCoefficientTildeAdjunction (R := R) H).unit.app M) := by
    change IsIso (((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/--
概要：H 加群値のアフィン係数大域切断は右随伴である。
方針：実際に構成した tilde との随伴を使う。
規約：H の非可換性・非平坦性を許す。
使われ方：TT §3、Toën §3.2 の右導来大域切断。
-/
instance affineCoefficientΓ_isRightAdjoint : (affineCoefficientΓ (R := R) H).IsRightAdjoint :=
  (affineCoefficientTildeAdjunction (R := R) H).isRightAdjoint

/--
概要：アフィン係数大域切断は実際の係数加群層の injective 対象を H 加群の injective へ送る。
方針：既証の完全な tilde 左随伴の mono 保存から右随伴の injective 保存を得る。
規約：固定環への単なる忘却の injective 保存とは区別する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 導来比較。
-/
instance affineCoefficientΓ_preservesInjectiveObjects :
    (affineCoefficientΓ (R := R) H).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (affineCoefficientTildeAdjunction (R := R) H)

end SerrePositivity.KST.DerivedGeometry
