module
public import SerrePositivity.DifferentialGraded.Module.Left
public import SerrePositivity.DifferentialGraded.Module.Category

/-! # 全Hom endを持つ左dg加群圏

既存の左加群対象に、Dᵒᵖ上の右加群との比較を通じて豊穣を入れる。
通常の関手圏の自然性を全次数Homの代用にしない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群のHomは二重opposite表示の主Hom end。 -/
abbrev leftModuleHom (M N : LeftModule A D) : Complex A :=
  moduleHom A Dᵒᵖ M.toRightOpposite N.toRightOpposite

instance leftModuleEnrichment : DGCategory A (LeftModule A D) :=
  ofHomObjects A (LeftModule A D) (leftModuleHom A D)
    (fun M => moduleIdentity A Dᵒᵖ M.toRightOpposite)
    (fun M N P => moduleComposition A Dᵒᵖ M.toRightOpposite N.toRightOpposite P.toRightOpposite)
    (fun M N => moduleIdentity_comp A Dᵒᵖ M.toRightOpposite N.toRightOpposite)
    (fun M N => moduleComp_identity A Dᵒᵖ M.toRightOpposite N.toRightOpposite)
    (fun M N P Q => moduleComposition_assoc A Dᵒᵖ
      M.toRightOpposite N.toRightOpposite P.toRightOpposite Q.toRightOpposite)

abbrev LeftModuleCategory := ClosedCategory A (LeftModule A D)

/-- 対象比較と恒等Homからなるdg関手。 -/
def leftModuleToRightOppositeDG : DGFunctor A (LeftModule A D) (RightModule A Dᵒᵖ) where
  obj := LeftModule.toRightOpposite
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp M N P := by
    change moduleComposition A Dᵒᵖ M.toRightOpposite N.toRightOpposite P.toRightOpposite ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ moduleComposition A Dᵒᵖ
        M.toRightOpposite N.toRightOpposite P.toRightOpposite
    simp

def leftModuleToRightOpposite : LeftModuleCategory A D ⥤ ModuleCategory A Dᵒᵖ :=
  (leftModuleToRightOppositeDG A D).onClosed

/-- 主Hom endを評価する左加群のdg評価関手。 -/
def leftModuleEvaluationDG (x : D) : DGFunctor A (LeftModule A D) (Complex A) where
  obj N := N.obj x
  map M N := moduleHomπ A Dᵒᵖ M.toRightOpposite N.toRightOpposite (op x)
  map_id M := moduleIdentity_π A Dᵒᵖ M.toRightOpposite (op x)
  map_comp M N P := moduleComposition_π A Dᵒᵖ
    M.toRightOpposite N.toRightOpposite P.toRightOpposite (op x)

def leftModuleEvaluation (x : D) : LeftModuleCategory A D ⥤ Complex A :=
  (leftModuleEvaluationDG A D x).onClosed ⋙ closedToComplex A

end SerrePositivity.DifferentialGraded
