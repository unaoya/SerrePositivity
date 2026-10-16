module
public import SerrePositivity.DifferentialGraded.Bimodule.ParameterEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule
public import SerrePositivity.DifferentialGraded.Tensor.ParameterLeft
public import SerrePositivity.DifferentialGraded.Tensor.ParameterRight

/-! # 任意パラメータのbimodule変換の相対tensorへの値ごとの作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {K : Complex A}

/-- 前の合成因子Pの変換を値ごとに作用させる。 -/
def firstParamValue {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P' Q).value b e :=
  BalancedTensor.leftParamMap A C (Q.rightAt e)
    (Bimodule.paramLeftAt A B C τ b).app (Bimodule.paramLeftAt A B C τ b).naturality

/-- 後の合成因子Qの変換を値ごとに作用させる。 -/
def secondParamValue (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    K ⊗ (compose A B C E P Q).value b e ⟶ (compose A B C E P Q').value b e :=
  BalancedTensor.rightParamMap A C (P.leftAt b)
    (Bimodule.paramRightAt A C E τ e).app (Bimodule.paramRightAt A C E τ e).naturality

/-- P変数の作用ではパラメータがQの値を横切る。 -/
lemma firstParamValue_element {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (c : C) (e : E)
    {k r s n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hn : k + (r + s) = n) :
    (firstParamValue A B C E Q τ b e).f n
      (ιTensorObj K ((compose A B C E P Q).value b e) k (r + s) n hn
        (t ⊗ₜ[A] BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v rfl)) =
    (k * r).negOnePow • BalancedTensor.element A C (Q.rightAt e) (P'.leftAt b) c q
      ((((Bimodule.paramValue A B C τ b c).f k t).v s (k + s) (by omega)) v)
      (by omega) :=
  BalancedTensor.leftParamMap_element A C (Q.rightAt e)
    (Bimodule.paramLeftAt A B C τ b).app (Bimodule.paramLeftAt A B C τ b).naturality
    c t q v hn

/-- Q変数の作用では追加の交差符号はない。 -/
lemma secondParamValue_element (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (c : C) (e : E)
    {k r s n : ℤ} (t : K.X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hn : k + (r + s) = n) :
    (secondParamValue A B C E P τ b e).f n
      (ιTensorObj K ((compose A B C E P Q).value b e) k (r + s) n hn
        (t ⊗ₜ[A] BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v rfl)) =
    BalancedTensor.element A C (Q'.rightAt e) (P.leftAt b) c
      ((((Bimodule.paramValue A C E τ c e).f k t).v r (k + r) (by omega)) q) v
      (by omega) :=
  BalancedTensor.rightParamMap_element A C (P.leftAt b)
    (Bimodule.paramRightAt A C E τ e).app (Bimodule.paramRightAt A C E τ e).naturality
    c t q v hn

/-- P変数の作用の主Hom複体表示。 -/
def firstParamHom {P P' : Bimodule A B C} (Q : Bimodule A C E)
    (τ : BimoduleParamTrans A B C K P P') (b : B) (e : E) :
    K ⟶ homComplex A ((compose A B C E P Q).value b e)
      ((compose A B C E P' Q).value b e) := curryRight (firstParamValue A B C E Q τ b e)

/-- Q変数の作用の主Hom複体表示。 -/
def secondParamHom (P : Bimodule A B C) {Q Q' : Bimodule A C E}
    (τ : BimoduleParamTrans A C E K Q Q') (b : B) (e : E) :
    K ⟶ homComplex A ((compose A B C E P Q).value b e)
      ((compose A B C E P Q').value b e) := curryRight (secondParamValue A B C E P τ b e)

end SerrePositivity.DifferentialGraded.BimoduleTensor
