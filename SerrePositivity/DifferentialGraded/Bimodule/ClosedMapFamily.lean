module
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedComponents
public import SerrePositivity.DifferentialGraded.Module.HomSquareComposition

/-! # 全Hom自然な右加群射族による閉零bimodule射の表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B加群射を成分とし、左C作用の全Hom自然性を持つ射族。 -/
abbrev ClosedMapFamily (M N : Bimodule A B C) :=
  {a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c) //
    ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c') =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c)}

/-- 単位パラメータの全次数変換と全Hom自然な加群射族の同値。 -/
def closedMapFamilyEquiv (M N : Bimodule A B C) :
    BimoduleParamTrans A B C (𝟙_ (Complex A)) M N ≃ ClosedMapFamily A B C M N where
  toFun τ := ⟨closedTransApp A B C τ, closedTransApp_naturality A B C τ⟩
  invFun a := closedFamilyTrans A B C a.val a.property
  left_inv := closedFamilyTrans_closedTransApp A B C
  right_inv a := by apply Subtype.ext; rfl

/-- 閉零bimodule射族の恒等射。 -/
def closedMapFamilyId (M : Bimodule A B C) : ClosedMapFamily A B C M M :=
  ⟨fun _ => 𝟙 _, fun c c' => moduleHom_square_id A B (M.toFunctor.map c c')⟩

/-- 全次数自然性を保つbimodule射族の合成。 -/
def closedMapFamilyComp {M N P : Bimodule A B C}
    (a : ClosedMapFamily A B C M N) (b : ClosedMapFamily A B C N P) :
    ClosedMapFamily A B C M P :=
  ⟨fun c => a.val c ≫ b.val c, fun c c' =>
    moduleHom_square_comp A B (M.toFunctor.map c c') (N.toFunctor.map c c')
      (P.toFunctor.map c c') (a.val c) (a.val c') (b.val c) (b.val c')
      (a.property c c') (b.property c c')⟩

end SerrePositivity.DifferentialGraded.Bimodule
