module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent

/-! # 指定された関手同型を、任意のパラメーターの元の頂点で評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- 始域の quasicategory 性を要求せず、同じ同型を指定頂点で評価する。 -/
def functorIsoValue {K Y : SSet.{u}} {F G : K ⟶ Y} (e : FunctorIso F G) (x : K _⦋0⦌) :
    VertexIso (F.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) x) :=
  (eqToIso (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x F))).symm ≪≫
    VertexIso.map e (evaluateFunctorAt x) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x G))

/-- 同じ評価同型の順方向射は、同じ二胞体の指定点での評価。 -/
theorem functorIsoValue_hom {K Y : SSet.{u}} {F G : K ⟶ Y}
    (e : FunctorIso F G) (x : K _⦋0⦌) :
    (functorIsoValue e x).hom = functorHomEvaluate e.hom x := rfl

/-- 通常の成分が定義されるとき、同じ評価は元の指定成分に厳密に一致する。 -/
theorem functorIsoValue_eq_app {K Y : SSet.{u}} [Quasicategory K] [Quasicategory Y]
    {F G : K ⟶ Y} (e : FunctorIso F G) (x : K _⦋0⦌) :
    functorIsoValue e x = e.app x := by
  apply Iso.ext
  rw [functorIsoValue_hom, functorIso_app_hom_evaluate]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue_eq_app := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_eq_app

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue_hom := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIsoValue._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue._proof_1
