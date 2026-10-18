module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistAction

/-!
概要：KST §3.1 の捻り作用の指定比較を各頂点で計算する。
方針：係数 dg 自己関手が対象を固定することと標準制限比較の評価を使う。
規約：捻りの指数による対象移送も明示して恒等成分を確認する。
使われ方：捻り作用の結合・単位整合性を加群射の等式として証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：捻りで送った加群射の各頂点成分は元の成分。
方針：制限関手の評価公式と gauge の対象固定を使う。
規約：KST §3.1。使われ方：反復捻りの射の評価を直接計算する。 -/
theorem finiteOverlapTwistAction_map_eval (m : ℤ)
    {M N : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)} (f : M ⟶ N)
    (x : (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ) :
    (moduleEvaluation R _ x).map ((finiteOverlapTwistAction R a m).map f) =
      (moduleEvaluation R _ x).map f :=
  moduleRestriction_map_eval R _ _ (finiteOverlapTwistDGFunctor R a m).op.op f x

/-- 概要：捻り作用の単位比較の各頂点成分は恒等。
方針：標準制限単位比較の対象移送を、対象を固定することから消去する。
規約：KST §3.1。使われ方：捻り作用の左右単位条件。 -/
theorem finiteOverlapTwistActionZeroIso_eval
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (x : (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ) :
    (moduleEvaluation R _ x).map ((finiteOverlapTwistActionZeroIso R a).hom.app M) = 𝟙 _ := by
  unfold finiteOverlapTwistActionZeroIso
  rw [transitionRestrictionIdIso_eval]
  rfl

/-- 概要：捻り作用の加法比較の各頂点成分は恒等。
方針：標準制限合成比較の対象移送を、対象を固定することから消去する。
規約：KST §3.1。使われ方：捻り作用の結合条件。 -/
theorem finiteOverlapTwistActionAddIso_eval (m n : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (x : (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ) :
    (moduleEvaluation R _ x).map ((finiteOverlapTwistActionAddIso R a m n).hom.app M) = 𝟙 _ := by
  unfold finiteOverlapTwistActionAddIso
  rw [transitionRestrictionCompIso_eval]
  rfl

/-- 概要：指数の等式で捻り対象を移送する射の各頂点成分は恒等。
方針：評価関手は等式移送を保ち、各頂点の複体は指数に依存しない。
規約：KST §3.1。使われ方：整数の結合律と単位律の移送を消去する。 -/
theorem finiteOverlapTwistAction_transport_eval {m n : ℤ} (h : m = n)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a))
    (x : (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ) :
    (moduleEvaluation R _ x).map
      (eqToHom (congrArg (fun k => (finiteOverlapTwistAction R a k).obj M) h)) = 𝟙 _ := by
  subst n
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]

end SerrePositivity.KST.DerivedBlowup
