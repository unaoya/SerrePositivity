module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeFunctor
public import SerrePositivity.KST.DerivedGeometry.CoefficientExact
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
概要：全係数加群層へのアフィン tilde 関手の完全性と余極限保存。
方針：O 加群層への忘却との自然比較を使って通常の tilde へ移す。
規約：係数の可換性・平坦性・有限生成性は不要。
使われ方：Bondal–van den Bergh Thm 3.1.1、TT §3、Toën §3.2 の実際の Dqc への導来化。
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
概要：全加群層への係数 tilde 関手は加法的。
方針：忘却後の通常の tilde との自然同型と忘却の忠実性を使う。
規約：係数加群層の元の射の加法を保持する。
使われ方：Toën §3.2 のアフィン係数複体の導来化。
-/
instance affineCoefficientTildeFunctor_additive :
    (affineCoefficientTildeFunctor (R := R) H).Additive := by
  have : (affineCoefficientTildeFunctor (R := R) H ⋙
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget).Additive :=
    Functor.additive_of_iso (affineCoefficientTildeForgetIso H).symm
  exact Functor.additive_of_comp_faithful (affineCoefficientTildeFunctor H)
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget

/--
概要：全加群層への係数 tilde 関手は有限極限を保つ。
方針：忘却後の完全性を忘却の有限極限反映で戻す。
規約：H の平坦性は要求しない。
使われ方：TT §3、Toën §3.2 のアフィン係数 tilde の完全性。
-/
instance affineCoefficientTildeFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (affineCoefficientTildeFunctor (R := R) H) := by
  let G := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget
  have : PreservesFiniteLimits (affineCoefficientTildeFunctor (R := R) H ⋙ G) :=
    preservesFiniteLimits_of_natIso (affineCoefficientTildeForgetIso H).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (affineCoefficientTildeFunctor H) G

/--
概要：全加群層への係数 tilde 関手は小さい余極限を保つ。
方針：通常の tilde とスカラー制限の余極限保存を忘却の反映性で戻す。
規約：余極限は開ごとの切断でなく加群層の圏の余極限。
使われ方：Toën §3.2 のアフィン係数複体と余積。
-/
instance affineCoefficientTildeFunctor_preservesColimits :
    PreservesColimitsOfSize.{u,u} (affineCoefficientTildeFunctor (R := R) H) := by
  let G := (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget
  have : ReflectsColimitsOfSize.{u,u} G := reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u,u} (affineCoefficientTildeFunctor (R := R) H ⋙ G) :=
    preservesColimits_of_natIso (affineCoefficientTildeForgetIso H).symm
  exact preservesColimits_of_reflects_of_preserves (affineCoefficientTildeFunctor H) G

/--
概要：全加群層への係数 tilde 関手は有限余極限を保つ。
方針：小さい余極限保存を有限の場合に制限する。
規約：有限極限保存と合わせて実際の完全関手を与える。
使われ方：TT §3、Toën §3.2 の非有界導来関手。
-/
instance affineCoefficientTildeFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (affineCoefficientTildeFunctor (R := R) H) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/--
概要：係数 tilde 関手の像の基礎 O 加群層は準連接。
方針：アフィン係数同値の逆関手が準連接部分圏に値を持つことを使う。
規約：導来対象の各項の準連接性と Dqc の定義を区別する。
使われ方：Toën §3.2 の導来 tilde を実際の Dqc へ制限する入力。
-/
lemma affineCoefficientTildeFunctor_isQuasicoherent (M : ModuleCat.{u} H) :
    ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj
      ((affineCoefficientTildeFunctor (R := R) H).obj M)).IsQuasicoherent :=
  ((affineCoefficientEquivalence (R := R) H).inverse.obj M).property

/--
概要：全加群層への係数 tilde 関手は同型を反映する。
方針：圏同値の逆関手と充満部分圏の包含の同型反映を合成する。
規約：導来関手の完全忠実性をここから結論しない。
使われ方：Toën §3.2 の導来 tilde の保存性。
-/
instance affineCoefficientTildeFunctor_reflectsIsomorphisms :
    (affineCoefficientTildeFunctor (R := R) H).ReflectsIsomorphisms := by
  dsimp [affineCoefficientTildeFunctor, CoefficientSheaf.qcohInclusion]
  infer_instance

end SerrePositivity.KST.DerivedGeometry
