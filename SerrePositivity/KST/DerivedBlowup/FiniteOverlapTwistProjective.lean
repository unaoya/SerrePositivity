module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistEquivalence
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleProjectiveResolution
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionProjective

/-!
概要：KST v4 §3.1（pp.11–14）の整数捻りを全次数の dg 作用へ持ち上げ、ホモトピー射影性を保存する。
方針：逆捻りとの閉零随伴を H⁰ へ降ろし、擬同型を反転する Hom の判定を使う。
規約：原典とは異なる図式加群模型での証明。各頂点の射影性で代用しない。
使われ方：cartesian perfect な射影的 dg 模型上の捻り作用の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：全図式加群の整数捻りの dg 関手。
方針：既存の制限関手を全次数 Hom 上で使う。
規約：KST §3.1。使われ方：主加群圏の捻りを dg 模型へ接続する。 -/
abbrev finiteOverlapDGTwistAction (m : ℤ) :=
  dgModuleRestriction R (BlowupDiagramCoefficientObject R a)ᵒᵖ
    (BlowupDiagramCoefficientObject R a)ᵒᵖ (finiteOverlapTwistDGFunctor R a m).op.op

/-- 概要：全次数の捻りの閉零関手は指定通常捻りに一致する。
方針：既存 dg 制限の閉零計算を使う。
規約：KST §3.1。使われ方：指定自己同値から随伴を移す。 -/
theorem finiteOverlapDGTwistAction_onClosed (m : ℤ) :
    (finiteOverlapDGTwistAction R a m).onClosed = finiteOverlapTwistAction R a m :=
  dgModuleRestriction_onClosed_eq R _ _ _

/-- 概要：捻りと逆捻りの全 dg 関手の閉零随伴。
方針：構成済み自己同値の随伴を閉零関手の等式で移す。
規約：KST §3.1。使われ方：全次数 Hom 射影性の証明。 -/
def finiteOverlapDGTwistClosedAdjunction (m : ℤ) :
    (finiteOverlapDGTwistAction R a m).onClosed ⊣
      (finiteOverlapDGTwistAction R a (-m)).onClosed :=
  ((finiteOverlapTwistEquivalence R a m).toAdjunction.ofNatIsoLeft
    (eqToIso (finiteOverlapDGTwistAction_onClosed R a m)).symm).ofNatIsoRight
      (eqToIso (finiteOverlapDGTwistAction_onClosed R a (-m))).symm

/-- 概要：H⁰ 上でも捻りは逆捻りを右随伴に持つ。
方針：閉零随伴の単位・余単位を境界の商へ送る。
規約：KST §3.1。使われ方：擬同型を反転する Hom の比較。 -/
def finiteOverlapDGTwistHomotopyAdjunction (m : ℤ) :
    (finiteOverlapDGTwistAction R a m).onHomotopy ⊣
      (finiteOverlapDGTwistAction R a (-m)).onHomotopy :=
  DGFunctor.homotopyAdjunction _ _ (finiteOverlapDGTwistClosedAdjunction R a m)

/-- 概要：整数捻りは図式全体のホモトピー射影性を保つ。
方針：逆捻りが擬同型を保つので、随伴 Hom 同値で反転性を移す。
規約：KST §3.1、原典とは異なる dg 図式模型での証明。
使われ方：捻りを既存射影的 dg 模型へ制限する。 -/
theorem finiteOverlapTwistAction_homotopicallyProjective (m : ℤ)
    {P : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)}
    (hP : moduleHomotopicallyProjective R (BlowupDiagramCoefficientObject R a)ᵒᵖ P) :
    moduleHomotopicallyProjective R (BlowupDiagramCoefficientObject R a)ᵒᵖ
      ((finiteOverlapTwistAction R a m).obj P) := by
  apply moduleHomotopicallyProjective_of_coyoneda_inverts R _
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  let adj := finiteOverlapDGTwistHomotopyAdjunction R a m
  let Rf := (finiteOverlapDGTwistAction R a (-m)).onHomotopy.map f
  have hRf := dgModuleHomotopyRestriction_quasiIso R
    (BlowupDiagramCoefficientObject R a)ᵒᵖ (BlowupDiagramCoefficientObject R a)ᵒᵖ
    (finiteOverlapTwistDGFunctor R a (-m)).op f hf
  have hpost := (CategoryTheory.isIso_iff_bijective _).mp
    (moduleHomotopicallyProjective_coyoneda_inverts R _ hP Rf hRf)
  change Function.Bijective (fun s :
    (finiteOverlapDGTwistAction R a m).onHomotopy.obj ((moduleToHomotopy R _).obj P) ⟶ X =>
      s ≫ f)
  let eX := adj.homEquiv ((moduleToHomotopy R _).obj P) X
  let eY := adj.homEquiv ((moduleToHomotopy R _).obj P) Y
  have heq : (fun s :
      (finiteOverlapDGTwistAction R a m).onHomotopy.obj ((moduleToHomotopy R _).obj P) ⟶ X =>
        s ≫ f) = fun s => eY.symm (eX s ≫ Rf) := by
    funext s
    apply eY.injective
    rw [Equiv.apply_symm_apply]
    exact adj.homEquiv_naturality_right s f
  rw [heq]
  exact eY.symm.bijective.comp (hpost.comp eX.bijective)

end SerrePositivity.KST.DerivedBlowup
