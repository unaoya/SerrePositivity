module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent

/-! # 同じ指定関手同型の成分は、合成と逆を厳密に保つ -/

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
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F G H : X ⟶ Y} (e : FunctorIso F G) (f : FunctorIso G H) (x : X _⦋0⦌)

/-- 指定した合成の同じ実成分は、指定成分の合成。 -/
theorem functorIso_app_trans :
    FunctorIso.app (f := F) (g := H) (e ≪≫ f) x = e.app x ≪≫ f.app x := by
  apply Iso.ext
  simp only [Iso.trans_hom, functorIso_app_hom_evaluate, functorHomEvaluate_comp]

/-- 指定した逆同型の同じ実成分は、指定成分の逆。 -/
theorem functorIso_app_symm : FunctorIso.app (f := G) (g := F) e.symm x = (e.app x).symm := by
  apply Iso.ext
  simp only [Iso.symm_hom, functorIso_app_hom_evaluate, functorIso_app_inv_evaluate]

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIso_app_symm := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_symm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.functorIso_app_trans := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_trans
