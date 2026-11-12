module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：二つの指定収縮と閉零次射の交換の欠損に、明示的な次数 -2 の原始元を与える。
方針：二つの収縮を閉零次射の前後に合成し、Leibniz 則で微分を計算する。
規約：交換の厳密等号は主張しない。商パラメータの coherent 補正の最初の段階。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {x y : D} (hx : GradedHom R x x (-1)) (hy : GradedHom R y y (-1))
  (t : zeroCycles (homObject R D x y))

/-- 固定収縮の交換欠損に対する、同じ元だけを使った二次の補正。 -/
def dgContractionCommutatorPrimitive : GradedHom R x y (-2) :=
  -forward R (p := -1) (q := -1) (n := -2)
    (forward R (p := -1) (q := 0) (n := -1) hx t.val (by omega)) hy (by omega)

/-- 閉零次射に対する固定収縮の交換欠損は、明示的な境界である。 -/
lemma dgContractionCommutatorPrimitive_d
    (dhx : (homObject R D x x).d (-1) 0 hx = (unitElement R x).val)
    (dhy : (homObject R D y y).d (-1) 0 hy = (unitElement R y).val) :
    (homObject R D x y).d (-2) (-1) (dgContractionCommutatorPrimitive R hx hy t) =
      forward R (p := -1) (q := 0) (n := -1) hx t.val (by omega) -
        forward R (p := 0) (q := -1) (n := -1) t.val hy (by omega) := by
  rw [dgContractionCommutatorPrimitive, map_neg]
  change -(differential R (forward R (p := -1) (q := -1) (n := -2)
    (forward R (p := -1) (q := 0) (n := -1) hx t.val (by omega)) hy (by omega))) = _
  rw [differential_forward, differential_forward]
  have ht : differential R t.val = 0 := t.property
  change differential R hx = (unitElement R x).val at dhx
  change differential R hy = (unitElement R y).val at dhy
  rw [dhx, dhy, ht, forward_unit]
  have hz : forward R (p := -1) (q := 1) (n := 0) hx (0 : GradedHom R x y 1) (by omega) = 0 := by
    simp [forward]
  rw [hz]
  simp only [smul_zero, add_zero, unit_forward]
  norm_num
  abel

/-- Leibniz 則を、明示した前後の次数で使用する。 -/
lemma dgForwardDifferentialOfDegrees {z : D} {p q n p' q' n' : ℤ}
    (f : GradedHom R x y p) (g : GradedHom R y z q)
    (hpq : p + q = n) (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n') :
    (homObject R D x z).d n n' (forward R f g hpq) =
      forward R ((homObject R D x y).d p p' f) g (by omega) +
      p.negOnePow • forward R f ((homObject R D y z).d q q' g) (by omega) := by
  subst p' q' n'
  exact differential_forward R f g hpq

/-- 全次数で、固定収縮の交換欠損を補正する次数 -2 の作用。 -/
def dgGradedContractionPrimitive (k : ℤ) (a : GradedHom R x y k) :
    GradedHom R x y (k - 2) :=
  -k.negOnePow • forward R (p := k - 1) (q := -1) (n := k - 2)
    (forward R (p := -1) (q := k) (n := k - 1) hx a (by omega)) hy (by omega)

/-- 全次数の補正式。非閉元についても入力の微分項を保持する。 -/
lemma dgGradedContractionPrimitive_d (k : ℤ) (a : GradedHom R x y k)
    (dhx : (homObject R D x x).d (-1) 0 hx = (unitElement R x).val)
    (dhy : (homObject R D y y).d (-1) 0 hy = (unitElement R y).val) :
    (homObject R D x y).d (k - 2) (k - 1) (dgGradedContractionPrimitive R hx hy k a) =
      forward R (p := -1) (q := k) (n := k - 1) hx a (by omega) -
        k.negOnePow • forward R (p := k) (q := -1) (n := k - 1) a hy (by omega) +
      k.negOnePow • forward R (p := k) (q := -1) (n := k - 1)
        (forward R (p := -1) (q := k + 1) (n := k) hx
          ((homObject R D x y).d k (k + 1) a) (by omega)) hy (by omega) := by
  have hi := dgForwardDifferentialOfDegrees R hx a (n := k - 1)
    (p' := 0) (q' := k + 1) (n' := k) (by omega) (by omega) rfl (by omega)
  have ho := dgForwardDifferentialOfDegrees R
    (forward R (p := -1) (q := k) (n := k - 1) hx a (by omega)) hy
    (n := k - 2) (p' := k) (q' := 0) (n' := k - 1)
    (by omega) (by omega) (by omega) (by omega)
  rw [dhx] at hi
  rw [forward_unit] at hi
  rw [dhy] at ho
  rw [hi, unit_forward] at ho
  have hu : ∀ b : GradedHom R x y k, (-1 : ℤˣ) • b = -b := by
    intro b; simp [Units.smul_def]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, hu] at ho
  have hs : ∀ (b c : GradedHom R x y k),
      forward R (p := k) (q := -1) (n := k - 1) (b + -c) hy (by omega) =
        forward R (p := k) (q := -1) (n := k - 1) b hy (by omega) -
        forward R (p := k) (q := -1) (n := k - 1) c hy (by omega) := by
    intro b c
    simp [forward, TensorProduct.add_tmul, TensorProduct.neg_tmul, sub_eq_add_neg]
  rw [hs] at ho
  unfold dgGradedContractionPrimitive
  simp only [Units.smul_def, map_zsmul]
  rw [ho]
  have hsq : (k.negOnePow : ℤ) * (k.negOnePow : ℤ) = 1 := by
    exact congrArg (fun z : ℤˣ => (z : ℤ)) (Int.units_mul_self k.negOnePow)
  simp only [Int.negOnePow_sub, Int.negOnePow_one, Units.smul_def,
    Units.val_neg, Units.val_mul, Units.val_one, mul_neg, mul_one, neg_mul,
    neg_smul, smul_sub, smul_add, smul_smul, neg_neg, hsq, one_smul]
  abel
  simp only [neg_one_zsmul, smul_neg, neg_neg, smul_smul, hsq, one_smul]
  have hc : (-1 : ℤ) * ((k.negOnePow : ℤ) * (-1 * (k.negOnePow : ℤ))) = 1 := by
    calc
      _ = (k.negOnePow : ℤ) * (k.negOnePow : ℤ) := by ring
      _ = 1 := hsq
  rw [hc, one_smul]

/-- 閉じた任意次数の元では、微分項が消えて交換欠損の原始元となる。 -/
lemma dgGradedContractionPrimitive_d_of_closed (k : ℤ) (a : GradedHom R x y k)
    (dhx : (homObject R D x x).d (-1) 0 hx = (unitElement R x).val)
    (dhy : (homObject R D y y).d (-1) 0 hy = (unitElement R y).val)
    (ha : (homObject R D x y).d k (k + 1) a = 0) :
    (homObject R D x y).d (k - 2) (k - 1) (dgGradedContractionPrimitive R hx hy k a) =
      forward R (p := -1) (q := k) (n := k - 1) hx a (by omega) -
        k.negOnePow • forward R (p := k) (q := -1) (n := k - 1) a hy (by omega) := by
  rw [dgGradedContractionPrimitive_d R hx hy k a dhx dhy, ha]
  have hz : forward R (p := -1) (q := k + 1) (n := k) hx
      (0 : GradedHom R x y (k + 1)) (by omega) = 0 := by simp [forward]
  have hz' : forward R (p := k) (q := -1) (n := k - 1)
      (0 : GradedHom R x y k) hy (by omega) = 0 := by simp [forward]
  rw [hz, hz', smul_zero, add_zero]

/-- 二次補正は、元の dg 関手による全次数作用と厳密に可換する。 -/
lemma dgGradedContractionPrimitive_map {E : Type v} [DGCategory R E]
    (F : DGFunctor R D E) (k : ℤ) (a : GradedHom R x y k) :
    (F.map x y).f (k - 2) (dgGradedContractionPrimitive R hx hy k a) =
      dgGradedContractionPrimitive R ((F.map x x).f (-1) hx)
        ((F.map y y).f (-1) hy) k ((F.map x y).f k a) := by
  simp only [dgGradedContractionPrimitive, Units.smul_def, map_zsmul, F.map_forward]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
