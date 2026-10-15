module
public import SerrePositivity.DifferentialGraded.Bimodule.OfActions
public import SerrePositivity.DifferentialGraded.Category.TensorMixed

/-! # tensor積dg圏上の関手の左右への制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C]

/-- 右B・左C作用をuncurriedに表示する豊穣関手。 -/
abbrev BimoduleTensorFunctor := DGFunctor A (DGTensorCategory A Bᵒᵖ C) (Complex A)

namespace BimoduleTensorFunctor
variable {A B C}

/-- Cの対象を固定して右B加群へ制限する。 -/
def rightAt (F : BimoduleTensorFunctor A B C) (c : C) : RightModule A B :=
  (dgTensorIncludeFirst A Bᵒᵖ C c).comp F

/-- Bの対象を固定して左C加群へ制限する。 -/
def leftAt (F : BimoduleTensorFunctor A B C) (b : B) : LeftModule A C :=
  (dgTensorIncludeSecond A Bᵒᵖ C (op b)).comp F

/-- 制限された二作用は全次数でKoszul交換則を満たす。 -/
lemma interchange (F : BimoduleTensorFunctor A B C) {x y : Bᵒᵖ} {c d : C} {p q : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) :
    (((F.rightAt c).map x y).f p f).comp (((F.leftAt y.unop).map c d).f q g)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • ((((F.leftAt x.unop).map c d).f q g).comp
        (((F.rightAt d).map x y).f p f) rfl) := by
  change (((F.map (x, c) (y, c)).f p
      ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)).comp
      ((F.map (y, c) (y, d)).f q ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g))
        (by omega : p + q = q + p)) =
    (q * p).negOnePow • (((F.map (x, c) (x, d)).f q
      ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)).comp
      ((F.map (x, d) (y, d)).f p ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f)) rfl)
  have h₁ := DGFunctor.map_forward A F (x := (x, c)) (y := (y, c)) (z := (y, d))
    ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)
    ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g) (by omega : p + q = q + p)
  rw [dgTensor_first_then_second] at h₁
  change (F.map (x, c) (y, d)).f (q + p)
      (dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega)) =
    (enrichedComposition (F.obj (x, c)) (F.obj (y, c)) (F.obj (y, d))).f (q + p)
      (ιTensorObj (homComplex A (F.obj (x, c)) (F.obj (y, c)))
        (homComplex A (F.obj (y, c)) (F.obj (y, d))) p q (q + p) (by omega)
        (((F.map (x, c) (y, c)).f p ((dgTensorFirstHom A Bᵒᵖ C c x y).f p f)) ⊗ₜ[A]
          ((F.map (y, c) (y, d)).f q ((dgTensorSecondHom A Bᵒᵖ C y c d).f q g)))) at h₁
  rw [enrichedComposition_apply, mul_comm p q] at h₁
  have h₂ := DGFunctor.map_forward A F (x := (x, c)) (y := (x, d)) (z := (y, d))
    ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)
    ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f) rfl
  rw [dgTensor_second_then_first] at h₂
  change (F.map (x, c) (y, d)).f (q + p)
      ((q * p).negOnePow • dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega)) =
    (enrichedComposition (F.obj (x, c)) (F.obj (x, d)) (F.obj (y, d))).f (q + p)
      (ιTensorObj (homComplex A (F.obj (x, c)) (F.obj (x, d)))
        (homComplex A (F.obj (x, d)) (F.obj (y, d))) q p (q + p) rfl
        (((F.map (x, c) (x, d)).f q ((dgTensorSecondHom A Bᵒᵖ C x c d).f q g)) ⊗ₜ[A]
          ((F.map (x, d) (y, d)).f p ((dgTensorFirstHom A Bᵒᵖ C d x y).f p f)))) at h₂
  rw [enrichedComposition_apply] at h₂
  simp only [Units.smul_def, map_zsmul] at h₁ h₂
  rw [h₁] at h₂
  simpa only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul] using h₂

variable [Small.{u} B]

/-- 左作用は閉零自然性でなく、右B加群間の全次数自然変換を与える。 -/
def paramTrans (F : BimoduleTensorFunctor A B C) (c d : C) :
    ModuleParamTrans A B (c ⟶[Complex A] d) (F.rightAt c) (F.rightAt d) where
  app b := (F.leftAt b.unop).map c d
  naturality x y := moduleParamNaturality_of_cochain A (D := B)
    (K := c ⟶[Complex A] d) (M := F.rightAt c) (N := F.rightAt d)
    (fun b : Bᵒᵖ => (F.leftAt b.unop).map c d)
    (fun x y k p m hm t f => by
      subst m
      exact F.interchange f t) x y

/-- tensor積上の豊穣関手をcurriedなbimoduleへ変換する。 -/
def toBimodule (F : BimoduleTensorFunctor A B C) : Bimodule A B C :=
  Bimodule.ofParamTrans A B C F.rightAt F.paramTrans
    (fun c b => (F.leftAt b.unop).map_id c)
    (fun c d e b => (F.leftAt b.unop).map_comp c d e)

/-- 得られる左作用の全Hom end評価は元の制限関手のHom射。 -/
lemma toBimodule_map_π (F : BimoduleTensorFunctor A B C) (c d : C) (b : B) :
    F.toBimodule.toFunctor.map c d ≫
      moduleHomπ A B (F.rightAt c) (F.rightAt d) b = (F.leftAt b).map c d :=
  Bimodule.ofParamTrans_map_π A B C F.rightAt F.paramTrans _ _ c d b

end BimoduleTensorFunctor
end SerrePositivity.DifferentialGraded
