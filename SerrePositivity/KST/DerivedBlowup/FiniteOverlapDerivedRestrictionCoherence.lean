module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence

/-!
概要：KST §3.1 の有限重なりに沿う導来制限の標準単位・合成同型。
方針：一般の導来制限比較を構成済み局所 dg 遷移へ適用する。
規約：各同型の局所化前の成分は指定した加群制限の経路で計算する。
使われ方：canonical な導来局所比較の単位・三重条件の行先を固定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：恒等有限重なりの局所導来制限から恒等関手への標準同型。
方針：証明済みの dg 恒等律を一般の主導来比較へ適用する。
規約：KST §3.1。使われ方：指定導来局所比較の単位条件。 -/
abbrev finiteOverlapDerivedTransitionRestrictionIdIso (a : I → R)
    (T : FiniteOverlapIndex I) :=
  transitionDerivedRestrictionIdIso (finiteOverlapLocalDGTransition R a (le_refl T))
    (finiteOverlapLocalDGTransition_id R a T)

/-- 概要：二段の有限重なりの局所導来制限から直接制限への標準同型。
方針：証明済みの dg 合成律を一般の主導来比較へ適用する。
規約：KST §3.1。使われ方：指定導来比較の三重条件の行先を揃える。 -/
abbrev finiteOverlapDerivedTransitionRestrictionCompIso (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V) :=
  transitionDerivedRestrictionCompIso (finiteOverlapLocalDGTransition R a h)
    (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
    (finiteOverlapLocalDGTransition_comp R a h g)

/-- 概要：局所導来制限の単位同型は実加群上で指定の計算経路を持つ。
方針：延長した自然同型の順成分の計算公式を適用する。
規約：KST §3.1、一般補題の型を継承して局所化係数構造の再展開を避ける。
使われ方：指定導来比較を局所化前の単位条件へ戻す。 -/
theorem finiteOverlapDerivedTransitionRestrictionIdIso_hom_app (a : I → R)
    (T : FiniteOverlapIndex I) (M : ModuleCategory R (FiniteOverlapVertexObject R a T)ᵒᵖ) :
    type_of% (moduleDerivedIsoExtension_hom_app
      (transitionDerivedRestrictionIdPreIso (finiteOverlapLocalDGTransition R a (le_refl T))
        (finiteOverlapLocalDGTransition_id R a T)) M) :=
  moduleDerivedIsoExtension_hom_app
    (transitionDerivedRestrictionIdPreIso (finiteOverlapLocalDGTransition R a (le_refl T))
      (finiteOverlapLocalDGTransition_id R a T)) M

/-- 概要：局所導来制限の合成同型は実加群上で指定の計算経路を持つ。
方針：延長した自然同型の順成分の計算公式を適用する。
規約：KST §3.1、一般補題の型を継承する。
使われ方：指定導来比較を局所化前の三重条件へ戻す。 -/
theorem finiteOverlapDerivedTransitionRestrictionCompIso_hom_app (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V)
    (M : ModuleCategory R (FiniteOverlapVertexObject R a V)ᵒᵖ) :
    type_of% (moduleDerivedIsoExtension_hom_app
      (transitionDerivedRestrictionCompPreIso (finiteOverlapLocalDGTransition R a h)
        (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
        (finiteOverlapLocalDGTransition_comp R a h g)) M) :=
  moduleDerivedIsoExtension_hom_app
    (transitionDerivedRestrictionCompPreIso (finiteOverlapLocalDGTransition R a h)
      (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
      (finiteOverlapLocalDGTransition_comp R a h g)) M

end SerrePositivity.KST.DerivedBlowup
