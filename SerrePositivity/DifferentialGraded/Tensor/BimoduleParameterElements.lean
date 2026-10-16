module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleParameterValues

/-! # 相対tensorのパラメータ作用のHom複体成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

lemma param_rightAction_units_smul {D : Type w} [DGCategory A D]
    (M : RightModule A D) {x y : Dᵒᵖ} {p r n : ℤ}
    (f : GradedHom A x y p) (u : ℤˣ) (v : (M.obj x).X r) (hn : r + p = n) :
    moduleAction A M f (u • v) hn = u • moduleAction A M f v hn :=
  map_zsmul (((M.map x y).f p f).v r n hn).hom (u : ℤ) v

lemma param_leftAction_units_smul {D : Type w} [DGCategory A D]
    (M : LeftModule A D) {x y : D} {p r n : ℤ}
    (f : GradedHom A x y p) (u : ℤˣ) (v : (M.obj x).X r) (hn : r + p = n) :
    leftAction A M f (u • v) hn = u • leftAction A M f v hn :=
  map_zsmul (((M.map x y).f p f).v r n hn).hom (u : ℤ) v

lemma param_element_units_smul_left (M : RightModule A C) (N : LeftModule A C) (c : C)
    {r s n : ℤ} (u : ℤˣ) (q : (M.obj (op c)).X r) (v : (N.obj c).X s)
    (hn : r + s = n) :
    BalancedTensor.element A C M N c (u • q) v hn =
      u • BalancedTensor.element A C M N c q v hn := by
  have ht : (u • q) ⊗ₜ[A] v = u • (q ⊗ₜ[A] v) :=
    map_zsmul ((TensorProduct.mk A _ _).flip v) (u : ℤ) q
  unfold BalancedTensor.element
  rw [ht]
  simp only [Units.smul_def, map_zsmul]

lemma firstParamHom_element {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) (e : E)
    {k r s i n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : i + k = n) :
    (((firstParamHom A B C E Q τ b e).f k t).v i n hn)
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) =
    (k * r).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P'.leftAt b) c q
      ((((Bimodule.paramValue A B C τ b c).f k t).v s (k + s) (by omega)) v) (by omega) := by
  subst i
  change (curryComponent (firstParamValue A B C E Q τ b e) k t).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact firstParamValue_element A B C E Q τ b c e (n := n) t q v (by omega)

lemma secondParamHom_element (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E)
    {k r s i n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : i + k = n) :
    (((secondParamHom A B C E P τ b e).f k t).v i n hn)
      (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) =
    BalancedTensor.element A C (Q'.rightAt e) (P.leftAt b) c
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q) v (by omega) := by
  subst i
  change (curryComponent (secondParamValue A B C E P τ b e) k t).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact secondParamValue_element A B C E P τ b c e (n := n) t q v (by omega)

end SerrePositivity.DifferentialGraded.BimoduleTensor
