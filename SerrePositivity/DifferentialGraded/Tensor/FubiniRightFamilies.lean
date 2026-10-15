module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniColumns
public import SerrePositivity.DifferentialGraded.Tensor.DegreeElementsExt
public import SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedElements

/-! # 二重balanced族の右反復coendへの降下 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

omit [Small.{u} E] in
/-- Cのbalanced関係を、外側tensorの二つの内側総次数を明示して適用する。 -/
lemma DoubleFamily.balanceC_of_sums {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c c' : C) (e : E) {k r p s i j n : ℤ}
    (hi : r + p + s = i) (hj : r + p + s = j) (hn : k + i = n)
    (t : (R.obj (op e)).X k) (q : (Q.value c' e).X r)
    (f : GradedHom A c c' p) (v : (N.obj c).X s) :
    (r * p).negOnePow • tripleElement A C E (n := n) (fun c e => (a.row e).val c)
      c e t (moduleAction A (Q.rightAt e) f q rfl) v hi hn =
    tripleElement A C E (i := j) (n := n) (fun c e => (a.row e).val c) c' e t q
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))
      (by omega) (by omega) := by
  subst i j
  exact paramFamily_balanced_element A C (a.row e) c c' t q f v hn

/-- E方向に降ろした族はCのbalanced関係も保つ。 -/
lemma columnDesc_balanced_element {Q : Bimodule A C E} {R : RightModule A E}
    {N : LeftModule A C} {T : Complex A} (a : DoubleFamily A C E Q R N T)
    (c c' : C) (l p s n : ℤ) (hn : l + p + s = n)
    (z : ((rightModule A C E Q R).obj (op c')).X l) (f : GradedHom A c c' p)
    (v : (N.obj c).X s) :
    (l * p).negOnePow • familyElement A C (columnDesc A C E a) c
      (moduleAction A (rightModule A C E Q R) f z rfl) v hn =
    familyElement A C (columnDesc A C E a) c' z
      (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))
      (by omega) := by
  let Z := rightModule A C E Q R
  let L : (Z.obj (op c')).X l →ₗ[A] T.X n :=
    ((l * p).negOnePow : ℤ) •
      ((columnDesc A C E a c).f n).hom.comp
        ((ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn).hom.comp
          (((TensorProduct.mk A ((Z.obj (op c)).X (l + p)) ((N.obj c).X s)).flip v).comp
            ((((Z.map (op c') (op c)).f p f).v l (l + p) rfl).hom)))
  let H : (Z.obj (op c')).X l →ₗ[A] T.X n :=
    ((columnDesc A C E a c').f n).hom.comp
      ((ιTensorObj (Z.obj (op c')) (N.obj c') l (p + s) n (by omega)).hom.comp
        ((TensorProduct.mk A ((Z.obj (op c')).X l) ((N.obj c').X (p + s))).flip
          (SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega))))
  have heq : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply degree_element_ext A E R (Q.leftAt c')
    intro e k r hl t q
    change (l * p).negOnePow • (columnDesc A C E a c).f n
      (ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn
        (moduleAction A Z f (element A E R (Q.leftAt c') e t q hl) rfl ⊗ₜ[A] v)) =
      (columnDesc A C E a c').f n
        (ιTensorObj (Z.obj (op c')) (N.obj c') l (p + s) n (by omega)
          (element A E R (Q.leftAt c') e t q hl ⊗ₜ[A]
            SerrePositivity.DifferentialGraded.leftAction A N (n := p + s) f v (by omega)))
    have hact := rightModule_action_element A C E Q R (op c') (op c) e
      (j := r + p) hl rfl (show l + p = l + p from rfl) f t q
    change moduleAction A Z f (element A E R (Q.leftAt c') e t q hl) rfl = _ at hact
    rw [hact]
    simp only [Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul]
    change (l * p).negOnePow • ((p * k).negOnePow •
      (columnDesc A C E a c).f n
        (ιTensorObj (Z.obj (op c)) (N.obj c) (l + p) s n hn
          (element A E R (Q.leftAt c) e t (moduleAction A (Q.rightAt e) f q rfl)
            (by omega) ⊗ₜ[A] v))) = _
    rw [columnDesc_element, columnDesc_element, smul_smul, ← Int.negOnePow_add]
    have hs : l * p + p * k = r * p + (k * p + k * p) := by
      rw [← hl]
      ring
    rw [hs, Int.negOnePow_add, Int.negOnePow_add, Int.units_mul_self, mul_one]
    exact a.balanceC_of_sums A C E c c' e (i := r + p + s) (j := r + (p + s))
      rfl (by omega) (by omega) t q f v
  exact congrArg (fun h => h z) heq

/-- 二重balanced族から右反復coendの外側へ渡すbalanced族。 -/
def rightFamily {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) :
    BalancedFamily A C (rightModule A C E Q R) N T :=
  balancedFamilyMk A C (columnDesc A C E a)
    (columnDesc_balanced_element A C E a)

/-- 二重balanced族の右反復coendへの降下。 -/
def rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) : rightObj A C E Q R N ⟶ T :=
  desc A C (rightModule A C E Q R) N (rightFamily A C E a)

@[reassoc (attr := simp)]
lemma rightι_rightDesc {Q : Bimodule A C E} {R : RightModule A E} {N : LeftModule A C}
    {T : Complex A} (a : DoubleFamily A C E Q R N T) (c : C) (e : E) :
    rightι A C E Q R N c e ≫ rightDesc A C E a = (a.row e).val c := by
  change (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ ι A C (rightModule A C E Q R) N c ≫
      desc A C (rightModule A C E Q R) N (rightFamily A C E a) = _
  rw [ι_desc]
  change (α_ (R.obj (op e)) (Q.value c e) (N.obj c)).inv ≫
    (ι A E R (Q.leftAt c) e ▷ N.obj c) ≫ columnDesc A C E a c = _
  rw [ι_columnDesc]
  simp only [columnMaps, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
