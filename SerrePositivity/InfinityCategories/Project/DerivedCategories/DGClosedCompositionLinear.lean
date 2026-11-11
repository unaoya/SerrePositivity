module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 閉零射との斉次合成の線形性と単位上の自然性

概要：閉零射との左右の合成を各次数の線形写像とし、単位の全次数像と可換にする。
方針：tensor の線形性と、単位複体の零次数への集中を使う。
規約：全整数次数を保持する。使われ方：自由 Hom の生成元から厳密自然性を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 後に作用する次数零射を固定した、任意次数の合成の線形写像。 -/
def dgZeroPostcomposeLinear {x y z : D} (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A y z 0) (k : ℤ) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k →ₗ[A] _root_.SerrePositivity.DifferentialGraded.GradedHom A x z k where
  toFun f := compose A g f (add_zero k)
  map_add' f f' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right g f f' _
  map_smul' a f := by
    simp only [compose, Int.mul_zero, Int.negOnePow_zero, one_smul, RingHom.id_apply]
    change ((eComp (Complex A) x y z).f k).hom
      ((ιTensorObj (homObject A D x y) (homObject A D y z) k 0 k (add_zero k)).hom
        ((a • f) ⊗ₜ[A] g)) =
      a • ((eComp (Complex A) x y z).f k).hom
        ((ιTensorObj (homObject A D x y) (homObject A D y z) k 0 k (add_zero k)).hom (f ⊗ₜ[A] g))
    rw [← TensorProduct.smul_tmul', LinearMap.map_smul, LinearMap.map_smul]

/-- 先に作用する次数零射を固定した、任意次数の合成の線形写像。 -/
def dgZeroPrecomposeLinear {x y z : D} (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y 0) (k : ℤ) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A y z k →ₗ[A] _root_.SerrePositivity.DifferentialGraded.GradedHom A x z k where
  toFun g := compose A g f (zero_add k)
  map_add' g g' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left g g' f _
  map_smul' a g := by
    simp only [compose, Int.zero_mul, Int.negOnePow_zero, one_smul, RingHom.id_apply]
    change ((eComp (Complex A) x y z).f k).hom
      ((ιTensorObj (homObject A D x y) (homObject A D y z) 0 k k (zero_add k)).hom
        (f ⊗ₜ[A] (a • g))) =
      a • ((eComp (Complex A) x y z).f k).hom
        ((ιTensorObj (homObject A D x y) (homObject A D y z) 0 k k (zero_add k)).hom (f ⊗ₜ[A] g))
    rw [TensorProduct.tmul_smul, LinearMap.map_smul, LinearMap.map_smul]

/-- 単位の次数零への評価は、元の閉単位のスカラー倍。 -/
lemma dgUnit_f_zero_smul (x : D) (a : A) :
    (eId (Complex A) x).f 0 a = a • (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val := by
  change (eId (Complex A) x).f 0 a = a • (eId (Complex A) x).f 0 (1 : A)
  simpa only [smul_eq_mul, mul_one] using ((eId (Complex A) x).f 0).hom.map_smul a (1 : A)

/-- 任意の斉次単位の像は、指定次数零射と可換。 -/
lemma dgZero_unit_naturality {x y : D} (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y 0) (k : ℤ)
    (a : (𝟙_ (_root_.SerrePositivity.DifferentialGraded.Complex A)).X k) :
    _root_.SerrePositivity.DifferentialGraded.compose A f ((eId (Complex A) x).f k a) (add_zero k) =
      _root_.SerrePositivity.DifferentialGraded.compose A ((eId (Complex A) y).f k a) f (zero_add k) := by
  by_cases hk : k = 0
  · subst k
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUnit_f_zero_smul, dgUnit_f_zero_smul]
    change (dgZeroPostcomposeLinear A D f 0) ((show A from a) • (unitElement A x).val) =
      (dgZeroPrecomposeLinear A D f 0) ((show A from a) • (unitElement A y).val)
    rw [map_smul, map_smul]
    exact congrArg ((show A from a) • ·) ((compose_unit A f).trans (unit_compose A f).symm)
  · have hz : IsZero ((𝟙_ (Complex A)).X k) :=
      isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) k hk
    have ha : a = 0 := (ModuleCat.subsingleton_of_isZero hz).elim _ _
    subst a
    simp only [map_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
