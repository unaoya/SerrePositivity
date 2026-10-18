module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientSectionsFunctor

/-!
# 準連接係数加群層のアフィン大域切断

概要：準連接係数加群層の大域切断は忠実で同型を反映する。
方針：R への忘却後の自然同型を通常の tilde 同値と比較する。
規約：完全充満性・本質的全射性・導来同値は別に証明する。
使われ方：KST D4・T1′、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：アフィン上で準連接な始域からの O 加群層の射は大域切断上の写像で決まる。
方針：tilde と大域切断の随伴の余単位の自然性と始域での同型性を使う。
規約：終域の準連接性は要求しない。
使われ方：KST D4・T1′、Toën §3.2 の大域切断からの係数線形性の判定。
-/
lemma affineUnderlyingHom_ext {M N : (Spec R).Modules} [M.IsQuasicoherent]
    {f g : M ⟶ N} (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := (tilde.adjunction (R := R)).counit.naturality f
  have hg := (tilde.adjunction (R := R)).counit.naturality g
  change tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ f at hf
  change tilde.map (moduleSpecΓFunctor.map g) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ g at hg
  exact hf.symm.trans ((congrArg (fun q => tilde.map q ≫ N.fromTildeΓ) h).trans hg)

/--
概要：準連接係数加群層の大域切断関手は忠実。
方針：R への忘却後は忠実な係数忘却と tilde 同値の逆の合成になる。
規約：H 作用の再構成による充満性はこの主張には含めない。
使われ方：KST D4、Toën §3.2 のアフィン加群圏の比較。
-/
instance affineQcohΓ_faithful : (affineQcohΓ (R := R) H).Faithful :=
  Functor.Faithful.of_comp_iso (affineQcohΓForgetIso H)

/--
概要：準連接係数加群層の大域切断関手は同型を反映する。
方針：R への忘却後の比較と、係数忘却および tilde 同値の同型反映を使う。
規約：全係数加群層ではなく準連接な基礎 O 加群を持つ部分圏での主張。
使われ方：KST D4・T1′、Toën §3.2 の保存的なアフィン比較。
-/
instance affineQcohΓ_reflectsIsomorphisms :
    (affineQcohΓ (R := R) H).ReflectsIsomorphisms := by
  have : (affineQcohΓ H ⋙ ModuleCat.restrictScalars (algebraMap R H)).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (affineQcohΓForgetIso H).symm
  exact reflectsIsomorphisms_of_comp (affineQcohΓ H)
    (ModuleCat.restrictScalars (algebraMap R H))

end SerrePositivity.KST.DerivedGeometry
