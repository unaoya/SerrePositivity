module
public import SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedElements

/-! # パラメータ付きbalanced族の斉次生成元からの構成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 固定次数の三重tensorからの線形射を純粋生成元で判定する。 -/
lemma triple_degree_linear_ext (P Q S : Complex A) (i : ℤ) {V : ModuleCat.{u} A}
    (f g : ((P ⊗ Q) ⊗ S).X i →ₗ[A] V)
    (h : ∀ (r p s : ℤ) (hi : r + p + s = i)
      (m : P.X r) (q : Q.X p) (v : S.X s),
      f (ιTensorObj (P ⊗ Q) S (r + p) s i hi
        (ιTensorObj P Q r p (r + p) rfl (m ⊗ₜ[A] q) ⊗ₜ[A] v)) =
      g (ιTensorObj (P ⊗ Q) S (r + p) s i hi
        (ιTensorObj P Q r p (r + p) rfl (m ⊗ₜ[A] q) ⊗ₜ[A] v))) : f = g := by
  have heq : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SerrePositivity.cochainTensorTriple_hom_ext P Q S i
    intro r p s hi
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro m q v
    exact h r p s hi m q v
  exact congrArg ModuleCat.Hom.hom heq

variable (D : Type v) [DGCategory A D]

/-- パラメータ付きの純粋生成元関係から、chain map族のbalanced性を復元する。 -/
def paramFamilyMk {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (a : ∀ x, K ⊗ (M.obj (op x) ⊗ N.obj x) ⟶ T)
    (hbal : ∀ (x y : D) (k r p s n : ℤ) (hn : k + (r + p + s) = n)
      (t : K.X k) (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (v : (N.obj x).X s),
      (r * p).negOnePow • (a x).f n
        (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k (r + p + s) n hn
          (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) (r + p) s (r + p + s) rfl
            (moduleAction A M f m rfl ⊗ₜ[A] v))) =
      (a y).f n
        (ιTensorObj K (M.obj (op y) ⊗ N.obj y) k (r + p + s) n (by omega)
          (t ⊗ₜ[A] ιTensorObj (M.obj (op y)) (N.obj y) r (p + s) (r + p + s) (by omega)
            (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A N
              (n := p + s) f v (by omega))))) : ParamFamily A D M N K T := by
  refine ⟨a, ?_⟩
  intro x y
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro k i hki
  apply ModuleCat.hom_ext
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro t
  apply triple_degree_linear_ext A (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x) i
  intro r p s hi m f v
  subst i
  change (a x).f n
    ((K ◁ (rightAction A D M x y ▷ N.obj x)).f n
      (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
        k (r + p + s) n hki
        (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
          (r + p) s (r + p + s) rfl
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] v)))) =
    (a y).f n
      ((K ◁ ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y)).f n
        (ιTensorObj K ((M.obj (op y) ⊗ (x ⟶[Complex A] y)) ⊗ N.obj x)
          k (r + p + s) n hki
          (t ⊗ₜ[A] ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x)
            (r + p) s (r + p + s) rfl
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] v))))
  simp only [whiskerLeft_comp, comp_f, ModuleCat.comp_apply]
  rw [whiskerLeft_apply, whiskerRight_apply, rightAction_apply,
    whiskerLeft_apply, associator_apply, whiskerLeft_apply, whiskerLeft_apply, leftAction_apply]
  have ht (z : (M.obj (op x) ⊗ N.obj x).X (r + p + s)) (j : ℤ) :
      t ⊗ₜ[A] (j • z) = j • (t ⊗ₜ[A] z) :=
    map_zsmul (TensorProduct.mk A _ _ t) j z
  simpa only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul, ht] using
    hbal x y k r p s n hki t m f v

end SerrePositivity.DifferentialGraded.BalancedTensor
