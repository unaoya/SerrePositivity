module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PushoutResidualMatrix

/-! # 逆 cofiber Hom 座標による境界の未知成分の方程式

概要：明示的な持ち上げの二包含・ホモトピー・対角との合成と、二つの微分方程式を検証する。
方針：三成分を評価し、残差行列の式を逆座標の微分へ渡す。
規約：整合条件を明示的に仮定する。使われ方：D7 の実際の coslice 境界の明示解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C X : Complex S}

/-- 概要：持ち上げの inclusionB 成分は指定右辺の符号倍。
方針：逆座標の該当成分を評価する。
規約：符号は q.negOnePow。使われ方：脚側未知成分を零とする方程式。 -/
lemma pushoutHomBoundaryLift_inclusionB (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1)) (rT : Cochain A X q) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionB f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)
      (zero_add (q + 1)) = q.negOnePow • rB := by
  have H := congrArg (fun z => z.2.1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_coordinates f g q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)).2.1 = _ at H
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_left_eq_comp] at H
  exact H

/-- 概要：持ち上げの inclusionC 成分は指定右辺の符号倍。
方針：逆座標の該当成分を評価する。
規約：符号は q.negOnePow。使われ方：脚側未知成分を零とする方程式。 -/
lemma pushoutHomBoundaryLift_inclusionC (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1)) (rT : Cochain A X q) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutInclusionC f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)
      (zero_add (q + 1)) = q.negOnePow • rC := by
  have H := congrArg (fun z => z.2.2)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_coordinates f g q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)).2.2 = _ at H
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_right_eq_comp] at H
  exact H

/-- 概要：持ち上げの標準ホモトピー成分は三角形側右辺の符号倍。
方針：逆座標の第一成分を評価する。
規約：一段低い次数。使われ方：二つの三角形成分を零とする方程式。 -/
lemma pushoutHomBoundaryLift_homotopy (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1)) (rT : Cochain A X q) :
    (mappingCone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberDifference f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)
      (by omega) = q.negOnePow • rT := by
  have H := congrArg (fun z => z.1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_coordinates f g q rB rC rT)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)).1 = _ at H
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_apex_eq_comp] at H
  exact H

/-- 概要：対角との合成は C 側右辺と g の前合成の符号倍。
方針：対角の C 側を通る分解と合成の結合律を使う。
規約：次数 q+1。使われ方：A 側の未知成分の微分。 -/
lemma pushoutHomBoundaryLift_diagonal (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1)) (rT : Cochain A X q) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC rT)
      (zero_add (q + 1)) =
      q.negOnePow • (Cochain.ofHom g).comp rC (zero_add (q + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    pushoutHomBoundaryLift_inclusionC, Cochain.comp_units_smul]

/-- 概要：四つの残差微分条件を満たす右辺から、後続成分の微分方程式の明示解を得る。
方針：残差行列の式を逆座標の微分へ代入する。
規約：r_A は二三角形で同じものを使う。使われ方：実際の未知成分の δa=r₀。 -/
lemma pushoutHomBoundaryLift_differential_of_residuals (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
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
    δ (q + 1) (q + 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC (rAB - rAC)) = r0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift_differential f g q rB rC (rAB - rAC) r0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutResidual_matrix f g q r0 rB rC rA rAB rAC hB hC hAB hAC)

/-- 概要：A 側未知成分を右三角形右辺の符号倍に取ると対角の微分方程式を満たす。
方針：右三角形の整合条件と持ち上げの対角成分を使い、符号の二乗を消す。
規約：他の四未知成分は零にできる形。使われ方：A 側の未知成分の検証。 -/
lemma pushoutBoundary_A_equation (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (rB : Cochain B X (q + 1)) (rC : Cochain C X (q + 1))
    (rA : Cochain A X (q + 1)) (rAB rAC : Cochain A X q)
    (hAC : δ q (q + 1) rAC = q.negOnePow •
      (rA - (Cochain.ofHom g).comp rC (zero_add (q + 1)))) :
    δ q (q + 1) (q.negOnePow • rAC) = rA - q.negOnePow •
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomBoundaryLift f g q rB rC (rAB - rAC)) (zero_add (q + 1)) := by
  rw [δ_units_smul, hAC, pushoutHomBoundaryLift_diagonal]
  simp only [smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
