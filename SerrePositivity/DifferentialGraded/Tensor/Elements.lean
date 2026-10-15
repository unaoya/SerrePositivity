module
public import SerrePositivity.DifferentialGraded.Tensor.Functor

/-! # balanced tensorの斉次要素・作用関係・両変数map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Limits Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対象xでの純粋斉次tensorの像。 -/
def element (M : RightModule A D) (N : LeftModule A D) (x : D) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) : (obj A D M N).X n :=
  (ι A D M N x).f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))

/-- balanced関係は右作用のKoszul符号を含む。 -/
lemma element_balanced (M : RightModule A D) (N : LeftModule A D) (x y : D)
    {a p b n : ℤ} (m : (M.obj (op y)).X a) (f : GradedHom A x y p)
    (t : (N.obj x).X b) (hn : a + p + b = n) :
    (a * p).negOnePow • element A D M N x
      (moduleAction A M (x := op y) (y := op x) f m rfl) t hn =
    element A D M N y m
      (SerrePositivity.DifferentialGraded.leftAction A N (x := x) (y := y)
        (n := p + b) f t (by omega)) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl (m ⊗ₜ[A] f) ⊗ₜ[A] t)))
    (condition A D M N x y)
  change (ι A D M N x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (ι A D M N y).f n
      ((M.obj (op y) ◁ leftAction A D N x y).f n
        ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
          (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (a + p) b n hn
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [element, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

lemma map_element {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') (x : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op x)).X r)
    (t : ((ForgetEnrichment.to (Complex A) N).obj x).X s) (hn : r + s = n) :
    (map A D f g).f n
      (element A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x m t hn) =
    element A D (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N') x
      (((moduleEvaluation A D x).map f).f r m) (((leftModuleEvaluation A D x).map g).f s t) hn := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj ((ForgetEnrichment.to (Complex A) M).obj (op x))
      ((ForgetEnrichment.to (Complex A) N).obj x) r s n hn (m ⊗ₜ[A] t))) (ι_map A D f g x)
  change (map A D f g).f n (element A D _ _ x m t hn) =
    (ι A D _ _ x).f n
      ((((moduleEvaluation A D x).map f) ⊗ₘ ((leftModuleEvaluation A D x).map g)).f n
        (ιTensorObj ((ForgetEnrichment.to (Complex A) M).obj (op x))
          ((ForgetEnrichment.to (Complex A) N).obj x) r s n hn (m ⊗ₜ[A] t))) at h
  let fx : (ForgetEnrichment.to (Complex A) M).obj (op x) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op x) := (moduleEvaluation A D x).map f
  let gx : (ForgetEnrichment.to (Complex A) N).obj x ⟶
      (ForgetEnrichment.to (Complex A) N').obj x := (leftModuleEvaluation A D x).map g
  have he := tensorMap_apply fx gx r s n hn m t
  exact h.trans (congrArg (fun z => (ι A D _ _ x).f n z) he)

end SerrePositivity.DifferentialGraded.BalancedTensor
