module
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomRightShift

/-! # 右シフトに沿う具体的な境界の保存と反映

概要：元の Hom とシフト Hom の実原始元を両方向に対応させる。
方針：包含との合成にも (-1)^n を掛け、Leibniz 則の符号を打ち消す。
規約：単なるホモロジー類の比較ではなく原始元を構成する。使われ方：相対境界の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の具体的な原始元から、シフト Hom の次数 −1 の原始元を構成する。 -/
lemma dgModuleHomRightShift_boundary {M N : RightModule A D} (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A M N n) (a : GradedHom A M N k)
    (ha : (moduleHom A D M N).d k n a = f) :
    (moduleHom A D M (shiftModule n N)).d (-1) 0
      (n.negOnePow • compose A (D := RightModule A D)
        (x := M) (y := N) (z := shiftModule n N) (p := k) (q := -n) (n := -1)
        (moduleShiftInElement A D n N) a (by omega)) = dgModuleHomRightShift A D n f := by
  subst n
  change differential A ((k + 1).negOnePow •
    compose A (moduleShiftInElement A D (k + 1) N) a (by omega)) = _
  have hi : differential A (D := RightModule A D) (x := N) (y := shiftModule (k + 1) N)
      (n := -(k + 1)) (moduleShiftInElement A D (k + 1) N) = 0 :=
    moduleShiftInElement_d A D (k + 1) N
  rw [differential_units_smul, differential_compose, hi, zero_compose, zero_add]
  change (k + 1).negOnePow • (-(k + 1)).negOnePow •
    compose A (D := RightModule A D) (x := M) (y := N) (z := shiftModule (k + 1) N)
      (p := k + 1) (q := -(k + 1)) (n := 0)
      (moduleShiftInElement A D (k + 1) N) ((moduleHom A D M N).d k (k + 1) a)
      (add_neg_cancel (k + 1)) = _
  rw [ha, smul_smul, ← Int.negOnePow_add, add_neg_cancel, Int.negOnePow_zero, one_smul]
  rfl

/-- 境界性は、正しい整数次数を保って右シフトで保存・反映される。 -/
lemma dgModuleHomRightShift_exists_primitive_iff {M N : RightModule A D} (n k : ℤ)
    (hkn : k + 1 = n) (f : GradedHom A M N n) :
    (∃ h : (moduleHom A D M (shiftModule n N)).X (-1),
      (moduleHom A D M (shiftModule n N)).d (-1) 0 h = dgModuleHomRightShift A D n f) ↔
      ∃ a : (moduleHom A D M N).X k, (moduleHom A D M N).d k n a = f := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨_, dgModuleHomRightShift_primitive A D n k hkn f h hh⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, dgModuleHomRightShift_boundary A D n k hkn f a ha⟩

end SerrePositivity.InfinityCategories
