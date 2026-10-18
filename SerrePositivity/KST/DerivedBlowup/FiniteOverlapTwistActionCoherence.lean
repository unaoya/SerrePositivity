module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistActionComponents

/-!
概要：KST §3.1 の整数捻り作用の加群圏上の結合・単位整合性。
方針：各加群射を全頂点で評価し、標準比較の恒等成分を使う。
規約：整数和の結合律・単位律による対象移送を表示する。
使われ方：捻りの反復合成の経路を固定し、導来圏上の整合性へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

set_option maxHeartbeats 2000000 in
-- 三段の制限作用と指数の対象移送の型を照合するために必要。
/-- 概要：捻り作用の三段合成は指数の結合律の移送を含めて整合する。
方針：全頂点で加法比較の恒等成分を使い、二つの合成を比較する。
規約：KST §3.1。使われ方：捻り作用の指定加法比較の結合条件。 -/
theorem finiteOverlapTwistActionAddIso_assoc (m n p : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapTwistActionAddIso R a m n).hom.app
        ((finiteOverlapTwistAction R a p).obj M) ≫
        (finiteOverlapTwistActionAddIso R a (m + n) p).hom.app M ≫
        eqToHom (congrArg (fun k => (finiteOverlapTwistAction R a k).obj M) (add_assoc m n p)) =
      (finiteOverlapTwistAction R a m).map
          ((finiteOverlapTwistActionAddIso R a n p).hom.app M) ≫
        (finiteOverlapTwistActionAddIso R a m (n + p)).hom.app M := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, finiteOverlapTwistActionAddIso_eval,
    finiteOverlapTwistActionAddIso_eval,
    finiteOverlapTwistAction_transport_eval R a (add_assoc m n p),
    finiteOverlapTwistAction_map_eval]
  rw [finiteOverlapTwistActionAddIso_eval, finiteOverlapTwistActionAddIso_eval]
  rfl

set_option maxHeartbeats 2000000 in
-- 零捻りと指数の左単位移送の対象を照合するために必要。
/-- 概要：加法比較で左の指数が零のとき、指定零捻り比較に一致する。
方針：各頂点で比較と指数移送の恒等成分を照合する。
規約：KST §3.1。使われ方：捻り作用の左単位条件。 -/
theorem finiteOverlapTwistActionAddIso_zero_left (m : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapTwistActionAddIso R a 0 m).hom.app M ≫
        eqToHom (congrArg (fun k => (finiteOverlapTwistAction R a k).obj M) (zero_add m)) =
      (finiteOverlapTwistActionZeroIso R a).hom.app
        ((finiteOverlapTwistAction R a m).obj M) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, finiteOverlapTwistActionAddIso_eval,
    finiteOverlapTwistAction_transport_eval R a (zero_add m), finiteOverlapTwistActionZeroIso_eval]
  exact Category.id_comp _

set_option maxHeartbeats 2000000 in
-- 零捻りと指数の右単位移送の対象を照合するために必要。
/-- 概要：加法比較で右の指数が零のとき、零捻り比較を作用で送った射に一致する。
方針：各頂点で比較の恒等成分と制限関手の評価公式を使う。
規約：KST §3.1。使われ方：捻り作用の右単位条件。 -/
theorem finiteOverlapTwistActionAddIso_zero_right (m : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapTwistActionAddIso R a m 0).hom.app M ≫
        eqToHom (congrArg (fun k => (finiteOverlapTwistAction R a k).obj M) (add_zero m)) =
      (finiteOverlapTwistAction R a m).map ((finiteOverlapTwistActionZeroIso R a).hom.app M) := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, finiteOverlapTwistActionAddIso_eval,
    finiteOverlapTwistAction_transport_eval R a (add_zero m), finiteOverlapTwistAction_map_eval]
  rw [finiteOverlapTwistActionZeroIso_eval]
  exact Category.id_comp _

end SerrePositivity.KST.DerivedBlowup
