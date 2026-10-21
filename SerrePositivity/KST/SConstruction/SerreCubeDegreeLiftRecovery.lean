module
public import SerrePositivity.KST.SConstruction.SerreCubeDegreeLift

/-! # 元の全 tensor 生成元の線形復元の値の回収
概要：元の全次数線形復元は、元の全端点・辺 tensor 生成元に指定した値を回収する。
方針：元の双次数包含上で再帰を評価し、区間と直前の cube の復元則を合成する。
規約：元の tensor 加群と全生成元を保持。使われ方：HA の指定面値からの逆 Hom 射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の次数線形復元は、全ての元の tensor 生成元に指定した値を厳密に回収する。 -/
lemma serreCubeDegreeLift_generator (n : ℕ) (k : ℤ) (V : ModuleCat.{u} A)
    (v : ∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → V)
    (i : SerreCubeGeneratorIndex n) (hi : serreCubeGeneratorDegree n i = k) :
    serreCubeDegreeLift A n k V v
        (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi) (serreCubeGenerator A n i)) =
      v i hi := by
  induction n generalizing k V with
  | zero =>
    have hei : i = PUnit.unit := by cases i; rfl
    subst i
    subst k
    unfold serreCubeDegreeLift
    erw [dite_eq_left rfl]
    change moduleElementMap A V (v PUnit.unit rfl)
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        (serreCubeGenerator A 0 PUnit.unit)) = v PUnit.unit rfl
    have hu : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        (serreCubeGenerator A 0 PUnit.unit) = 1 :=
      ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv_hom_id 1
    rw [hu]
    exact (moduleElementEquiv A V).apply_symm_apply (v PUnit.unit rfl)
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    let p := serreCubeGeneratorDegree n i
    let q := serreIntervalGeneratorDegree j
    have hpq : p + q = k := hi
    let values (a : SerreCubeGeneratorIndex n) (ha : serreCubeGeneratorDegree n a = p) :=
      (serreIntervalDegreeLift A q V (fun b hb =>
        v (a, b) ((congrArg₂ (fun x y : ℤ => x + y) ha hb).trans hpq))).hom
    have ho := ih p (ModuleCat.of A ((serreInterval A).X q →ₗ[A] V)) values i rfl
    have hv := congrArg (fun l : (serreInterval A).X q →ₗ[A] V => l (serreIntervalGenerator A j)) ho
    have hI := serreIntervalDegreeLift_generator A q V
      (fun b hb => v (i, b) ((congrArg₂ (fun x y : ℤ => x + y) rfl hb).trans hpq)) j rfl
    have hT := ConcreteCategory.congr_hom (serreCubeDegreeLift_succ_ι A n k V v p q hpq)
      (serreCubeGenerator A n i ⊗ₜ[A] serreIntervalGenerator A j)
    exact (congrArg (fun w => serreCubeDegreeLift A (n + 1) k V v w)
      (serreCubeGenerator_succ_cast A n i j k hi)).trans
        (hT.trans (hv.trans hI))

end SerrePositivity.KST.SConstruction
