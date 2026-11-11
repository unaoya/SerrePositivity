module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PushoutHomLift

/-! # cofiber の三成分の残差行列

概要：脚側と三角形側の四つの微分条件は、逆 Hom 座標による明示解の微分条件を与える。
方針：二三角形の条件を引き、二脚の条件と負一冪の二乗一を使って座標を比較する。
規約：可換環上の非有界複体、全整数次数。使われ方：D7 の明示解の微分方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C X : Complex S}

/-- 概要：六つの右辺の四微分条件は持ち上げの座標の微分行列を指定する。
方針：二脚をそれぞれ簡約し、第一座標では三角形条件の差と接続項を相殺する。
規約：この補題の条件は前提。使われ方：実際の境界の整合条件から明示解を得る。 -/
lemma pushoutResidual_matrix (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (r0 : Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (q + 1 + 1))
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1))
    (rA : Cochain A X (q + 1)) (rAB rAC : Cochain A X q)
    (hB : δ (q + 1) (q + 1 + 1) rB = q.negOnePow •
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)).comp r0 (zero_add (q + 1 + 1)))
    (hC : δ (q + 1) (q + 1 + 1) rC = q.negOnePow •
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).comp r0 (zero_add (q + 1 + 1)))
    (hAB : δ q (q + 1) rAB = q.negOnePow •
      ((mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)).comp r0 (by omega) + rA -
        (Cochain.ofHom f).comp rB (zero_add (q + 1))))
    (hAC : δ q (q + 1) rAC = q.negOnePow •
      (rA - (Cochain.ofHom g).comp rC (zero_add (q + 1)))) :
    (δ q (q + 1) (q.negOnePow • (rAB - rAC)) + (q + 1 + 1).negOnePow •
        ((Cochain.ofHom f).comp (q.negOnePow • rB) (zero_add (q + 1)) -
          (Cochain.ofHom g).comp (q.negOnePow • rC) (zero_add (q + 1))),
      (δ (q + 1) (q + 1 + 1) (q.negOnePow • rB),
        δ (q + 1) (q + 1 + 1) (q.negOnePow • rC))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g (q + 1) r0 := by
  have hs : (q + 1 + 1).negOnePow = q.negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add]
    norm_num
  apply Prod.ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_apex_eq_comp]
    simp only [δ_units_smul, δ_sub, hAB, hAC, Cochain.comp_units_smul, hs,
      smul_sub, smul_smul, Int.units_mul_self, one_smul]
    abel
  · apply Prod.ext
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_left_eq_comp]
      simp only [δ_units_smul, hB, smul_smul, Int.units_mul_self, one_smul]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_right_eq_comp]
      simp only [δ_units_smul, hC, smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
