module
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent

/-! # 同じ指定関手同型の成分は、合成と逆を厳密に保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
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

end SerrePositivity.KST.Fibration
