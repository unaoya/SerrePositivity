module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1B.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluation

/-! # 指定した関手同型の成分の値を、元の同じ二胞体の頂点評価として保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F G : X ⟶ Y} (e : FunctorIso F G) (x : X _⦋0⦌)

/-- 既存の同じ自然同型の実成分は、同じ二胞体の成分と厳密に一致する。 -/
theorem functorIso_app_hom_evaluate : (e.app x).hom = functorHomEvaluate e.hom x := by
  let E := VertexIso.map e (evaluateFunctorAt x)
  let E' : VertexIso (F.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) x) :=
    (eqToIso (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x F))).symm ≪≫
      E ≪≫ eqToIso (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x G))
  have he : HEq E' E := F2.iso_endpoints_heq E
    (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x F))
    (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x G))
  have ha : e.app x = E' :=
    eq_of_heq ((F2.functorIso_app_heq_evaluate e x).trans he.symm)
  exact congrArg (fun k => k.hom) ha

/-- 逆成分も、元の同じ逆二胞体の成分と厳密に一致する。 -/
theorem functorIso_app_inv_evaluate : (e.app x).inv = functorHomEvaluate e.inv x := by
  apply (cancel_epi (e.app x).hom).mp
  rw [Iso.hom_inv_id, functorIso_app_hom_evaluate,
    ← functorHomEvaluate_comp, e.hom_inv_id, functorHomEvaluate_id]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIso_app_hom_evaluate := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIso_app_inv_evaluate := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_inv_evaluate
