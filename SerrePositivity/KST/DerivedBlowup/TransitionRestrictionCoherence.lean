module

public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Functor.Closed

/-!
概要：KST §3.1 で用いる dg 遷移の等式に沿う加群制限の標準比較。
方針：一般の dg 圏で等式を消去してから既存の制限単位・合成同型を使う。
規約：対象の等式移送は評価公式にも明示する。
使われ方：局所化環上の具体的模型を展開せず標準比較を組み立てる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R]
variable {C : Type v} {D : Type w} {E : Type z}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  [Small.{u} C] [Small.{u} D] [Small.{u} E]

/-- 概要：指定の恒等 dg 遷移に沿う加群制限の単位同型。
方針：dg 関手の等式を消去して既存の単位比較を使う。
規約：KST §3.1。使われ方：具体的局所遷移の恒等比較。 -/
def transitionRestrictionIdIso (F : DGFunctor R C C) (h : F = DGFunctor.id C) :
    moduleRestriction R Cᵒᵖ Cᵒᵖ F.op.op ≅ 𝟭 _ := by
  subst F
  exact moduleRestrictionIdIso R Cᵒᵖ

/-- 概要：指定の合成 dg 遷移に沿う加群制限の合成同型。
方針：等式で直接遷移を合成へ戻し、既存の合成比較を使う。
規約：KST §3.1。使われ方：具体的局所遷移の三重比較。 -/
def transitionRestrictionCompIso (F : DGFunctor R C D) (G : DGFunctor R D E)
    (H : DGFunctor R C E) (h : F.comp G = H) :
    moduleRestriction R Dᵒᵖ Eᵒᵖ G.op.op ⋙ moduleRestriction R Cᵒᵖ Dᵒᵖ F.op.op ≅
      moduleRestriction R Cᵒᵖ Eᵒᵖ H.op.op := by
  subst H
  exact moduleRestrictionCompIso R Cᵒᵖ Dᵒᵖ Eᵒᵖ F.op.op G.op.op

/-- 概要：制限単位同型の成分は対象等式の複体への移送。
方針：関手等式を消去して既存の恒等評価へ戻す。
規約：KST §3.1。使われ方：指定比較の単位条件の評価。 -/
theorem transitionRestrictionIdIso_eval (F : DGFunctor R C C) (h : F = DGFunctor.id C)
    (M : ModuleCategory R Cᵒᵖ) (x : C) :
    (moduleEvaluation R Cᵒᵖ (op x)).map ((transitionRestrictionIdIso F h).hom.app M) =
      eqToHom (congrArg (fun K : DGFunctor R C C =>
        (ForgetEnrichment.to (Complex R) M).obj (op (op (K.obj x)))) h) := by
  subst F
  exact moduleRestrictionIdObjIso_hom_eval R Cᵒᵖ M (op x)

/-- 概要：制限合成同型の成分は対象等式の複体への移送。
方針：関手等式を消去して既存の合成比較の恒等評価へ戻す。
規約：KST §3.1。使われ方：指定比較の三重条件の評価。 -/
theorem transitionRestrictionCompIso_eval (F : DGFunctor R C D) (G : DGFunctor R D E)
    (H : DGFunctor R C E) (h : F.comp G = H) (M : ModuleCategory R Eᵒᵖ) (x : C) :
    (moduleEvaluation R Cᵒᵖ (op x)).map ((transitionRestrictionCompIso F G H h).hom.app M) =
      eqToHom (congrArg (fun K : DGFunctor R C E =>
        (ForgetEnrichment.to (Complex R) M).obj (op (op (K.obj x)))) h) := by
  subst H
  exact moduleRestrictionCompObjIso_hom_eval R Cᵒᵖ Dᵒᵖ Eᵒᵖ F.op.op G.op.op M (op x)

end SerrePositivity.KST.DerivedBlowup
