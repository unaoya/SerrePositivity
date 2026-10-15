module
public import SerrePositivity.DifferentialGraded.Module.ActionChain
public import SerrePositivity.DifferentialGraded.Module.LeftAction

/-! # balanced tensorの二つの作用射と成分の符号 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- M(y)⊗D(x,y)からM(x)への右作用。 -/
def rightAction (M : RightModule A D) (x y : D) :
    M.obj (op y) ⊗ (x ⟶[Complex A] y) ⟶ M.obj (op x) :=
  (signedSwap (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫
    moduleActionChain A M (op y) (op x)

/-- D(x,y)⊗N(x)からN(y)への左作用。 -/
def leftAction (N : LeftModule A D) (x y : D) :
    (x ⟶[Complex A] y) ⊗ N.obj x ⟶ N.obj y := uncurryRight (N.map x y)

/-- 右作用ではHomと加群値の順を交換する符号を保持する。 -/
lemma rightAction_apply (M : RightModule A D) (x y : D) (r p n : ℤ) (hn : r + p = n)
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) :
    (rightAction A D M x y).f n
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p n hn (m ⊗ₜ[A] f)) =
      (r * p).negOnePow • moduleAction A M f m hn := by
  change (uncurryRight (M.map (op y) (op x))).f n
    ((signedSwap (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p n hn (m ⊗ₜ[A] f))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun t : (M.obj (op x)).X n => ((r * p).negOnePow : ℤ) • t)
    (uncurryRight_apply (M.map (op y) (op x)) p r n (by omega) f m)

lemma leftAction_apply (N : LeftModule A D) (x y : D) (p r n : ℤ) (hn : p + r = n)
    (f : GradedHom A x y p) (m : (N.obj x).X r) :
    (leftAction A D N x y).f n
      (ιTensorObj (x ⟶[Complex A] y) (N.obj x) p r n hn (f ⊗ₜ[A] m)) =
      SerrePositivity.DifferentialGraded.leftAction A N f m (by omega) :=
  uncurryRight_apply (N.map x y) p r n hn f m

end SerrePositivity.DifferentialGraded.BalancedTensor
