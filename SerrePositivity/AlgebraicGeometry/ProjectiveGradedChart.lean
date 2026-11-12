module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveLaurentChart
public import Mathlib.Algebra.Module.GradedModule

/-!
概要：射影空間の標準開の交叉に、次数付き加群の斉次局所化を対応させる。
方針：標準開を狭めるとき、追加の変数の積の冪を分子に掛ける。
規約：指定した整数次数の分数を取る。Čech の項では非空の交叉だけを使う。
使われ方：斉次表示を Čech 複体へ送り、多項式環の捻りでは Laurent 複体に比較する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

universe u

variable {ι R : Type*} {M : Type u} [DecidableEq ι] [Fintype ι] [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]

/-- 標準開の分母の次数は反転する変数の個数。 -/
theorem projectiveLaurentDenominator_mem_polynomialGrade (R : Type*) [CommRing R]
    (T : Finset ι) :
    projectiveLaurentDenominator R T ∈
      AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (T.card : ℤ) := by
  apply (projectiveLaurentChartMap_mem_grade_iff R T _ _).mp
  rw [projectiveLaurentChartMap_denominator, ← projectiveLaurentDenominatorExponent_degree]
  exact AddMonoidAlgebra.single_mem_gradeBy _ _ _

variable (G : ℤ → Submodule R M)
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]

/-- 追加の分母の冪を掛けると、新しい分母に対応する次数成分へ移る。 -/
theorem projectiveGradedChart_mul_mem {T U : Finset ι} (h : T ⊆ U) (d : ℤ) (n : ℕ)
    (m : G (d + n • (T.card : ℤ))) :
    projectiveLaurentDenominator R (U \ T) ^ n • m.val ∈ G (d + n • (U.card : ℤ)) := by
  have hs := SetLike.GradedSMul.smul_mem
    (SetLike.pow_mem_graded n (projectiveLaurentDenominator_mem_polynomialGrade R (U \ T))) m.property
  have hc : ((U \ T).card : ℤ) + (T.card : ℤ) = (U.card : ℤ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card h
  have hd : n • ((U \ T).card : ℤ) +ᵥ (d + n • (T.card : ℤ)) = d + n • (U.card : ℤ) := by
    change (n • ((U \ T).card : ℤ) + (d + n • (T.card : ℤ))) = _
    rw [← hc, nsmul_add]
    ac_rfl
  exact hd ▸ hs

/-- 次数付き加群の指定次数の標準開係数図式。 -/
abbrev projectiveGradedModuleChartDiagram (d : ℤ) : Finset ι ⥤ ModuleCat R where
  obj T := ModuleCat.of R (projectiveGradedAway (projectiveLaurentDenominator R T)
    (fun n ↦ G (d + n • (T.card : ℤ))))
  map {T U} h := ModuleCat.ofHom
    (projectiveGradedAwayRestriction (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm
      (fun n ↦ G (d + n • (T.card : ℤ))) (fun n ↦ G (d + n • (U.card : ℤ)))
      (projectiveGradedChart_mul_mem G (leOfHom h) d))
  map_id T := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    simp [projectiveModuleAwayRestriction_refl]
  map_comp {T U V} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      projectiveGradedAwayRestriction_val]
    exact (LinearMap.congr_fun (projectiveModuleAwayRestriction_comp
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom f)).symm⟩)
      (show projectiveLaurentDenominator R U ∣ projectiveLaurentDenominator R V from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom g)).symm⟩)) z.val).symm

section GradedMaps

variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℤ → Submodule R N)
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) H]

/-- 分子と分母へ同じチャートの分母を掛けると、許された分子の次の次数へ移る。 -/
theorem projectiveGradedChart_mul_denominator (T : Finset ι) (d : ℤ) (n : ℕ)
    (m : G (d + n • (T.card : ℤ))) :
    projectiveLaurentDenominator R T • m.val ∈ G (d + (n + 1) • (T.card : ℤ)) := by
  have hs := SetLike.GradedSMul.smul_mem
    (projectiveLaurentDenominator_mem_polynomialGrade R T) m.property
  have hd : (T.card : ℤ) +ᵥ (d + n • (T.card : ℤ)) = d + (n + 1) • (T.card : ℤ) := by
    change ((T.card : ℤ) + (d + n • (T.card : ℤ))) = _
    rw [succ_nsmul]
    ac_rfl
  exact hd ▸ hs

/-- 次数を保つ加群写像は標準開の斉次局所化の自然変換を与える。 -/
def projectiveGradedModuleChartMap (d : ℤ) (f : M →ₗ[MvPolynomial ι R] N)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) :
    projectiveGradedModuleChartDiagram (ι := ι) G d ⟶ projectiveGradedModuleChartDiagram (ι := ι) H d where
  app T := ModuleCat.ofHom
    (projectiveGradedAwayMap (projectiveLaurentDenominator R T)
      (fun n ↦ G (d + n • (T.card : ℤ))) (fun n ↦ H (d + n • (T.card : ℤ)))
      f (fun _ ↦ hf _))
  naturality {T U} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    let p := projectiveLaurentDenominator R T
    let q := projectiveLaurentDenominator R U
    let a := projectiveLaurentDenominator R (U \ T)
    let V (n : ℕ) := G (d + n • (T.card : ℤ))
    let W (n : ℕ) := G (d + n • (U.card : ℤ))
    let V' (n : ℕ) := H (d + n • (T.card : ℤ))
    let W' (n : ℕ) := H (d + n • (U.card : ℤ))
    have ha : q = p * a := (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm
    have hs := projectiveGradedChart_mul_mem G (leOfHom h) d
    have hs' := projectiveGradedChart_mul_mem H (leOfHom h) d
    let zU := projectiveGradedAwayRestriction ha V W hs z
    let z' := projectiveGradedAwayMap p V V' f (fun _ ↦ hf _) z
    change (projectiveGradedAwayMap q W W' f (fun _ ↦ hf _) zU).val =
      (projectiveGradedAwayRestriction ha V' W' hs' z').val
    have hz : z.val ∈ projectiveGradedAway p V := z.property
    obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff p V
      (projectiveGradedChart_mul_denominator G T d) z.val).mp hz
    have hmU : projectiveGradedFraction q W n ⟨a ^ n • m.val, hs n m⟩ = zU.val := by
      dsimp only [zU]
      rw [projectiveGradedAwayRestriction_val, ← hm, projectiveGradedFraction_apply,
        projectiveGradedFraction_apply, projectiveModuleAwayRestriction_mk ha]
    have hm' := projectiveGradedAwayMap_fraction p V V' f (fun _ ↦ hf _) n m z hm
    rw [projectiveGradedAwayMap_fraction q W W' f (fun _ ↦ hf _) n _ zU hmU,
      projectiveGradedAwayRestriction_val, show z'.val =
        projectiveGradedFraction p V' n ⟨f m.val, hf _ _ m.property⟩ from hm']
    simp only [projectiveGradedFraction_apply, projectiveModuleAwayRestriction_mk ha, map_smul]

end GradedMaps

section Twists

variable (R : Type*) [CommRing R]

/-- 多項式環の次数成分は分母との積で次の成分へ移る。 -/
theorem projectivePolynomialGrade_mul_denominator (T : Finset ι) (d : ℤ) (n : ℕ)
    (m : AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (d + n • (T.card : ℤ))) :
    projectiveLaurentDenominator R T • m.val ∈
      AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
        (d + (n + 1) • (T.card : ℤ)) := by
  exact projectiveGradedChart_mul_denominator
    (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) T d n m

/-- Laurent の次数成分の基底による表示は、チャートの制限と可換。 -/
theorem projectiveLaurentGradeLinearEquiv_restrict {T U : Finset ι} (h : T ⊆ U)
    (d : ℤ) (a : AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d) :
    ((projectiveLaurentGradeLinearEquiv R U d).symm
      (Finsupp.lmapDomain R R (projectiveLaurentDegreeExponentRestriction h d)
        (projectiveLaurentGradeLinearEquiv R T d a))).val =
      projectiveLaurentChartRestriction R h a.val := by
  classical
  let A := AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree U) d
  let B := AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d
  have he :
      A.subtype.comp ((projectiveLaurentGradeLinearEquiv R U d).symm.toLinearMap.comp
        (Finsupp.lmapDomain R R (projectiveLaurentDegreeExponentRestriction h d))) =
      (projectiveLaurentChartRestriction R h).toLinearMap.comp
        (B.subtype.comp (projectiveLaurentGradeLinearEquiv R T d).symm.toLinearMap) := by
    apply Finsupp.lhom_ext
    intro e r
    change ((projectiveLaurentGradeLinearEquiv R U d).symm
      (Finsupp.mapDomain (projectiveLaurentDegreeExponentRestriction h d)
        (Finsupp.single e r))).val = projectiveLaurentChartRestriction R h
          ((projectiveLaurentGradeLinearEquiv R T d).symm (Finsupp.single e r)).val
    rw [Finsupp.mapDomain_single]
    apply AddMonoidAlgebra.coeff_injective
    change ((Finsupp.supportedEquivFinsupp (R := R)
        {e | projectiveLaurentDegree U e = d}).symm
        (Finsupp.single (projectiveLaurentDegreeExponentRestriction h d e) r) :
          projectiveLaurentExponents U →₀ R) =
      Finsupp.mapDomain (projectiveLaurentExponentRestriction h)
        ((Finsupp.supportedEquivFinsupp (R := R)
          {e | projectiveLaurentDegree T e = d}).symm
          (Finsupp.single e r) : projectiveLaurentExponents T →₀ R)
    rw [Finsupp.supportedEquivFinsupp_symm_single,
      Finsupp.supportedEquivFinsupp_symm_single, Finsupp.mapDomain_single]
    rfl
  simpa [LinearMap.comp_apply, A, B] using
    LinearMap.congr_fun he (projectiveLaurentGradeLinearEquiv R T d a)

/-- 同次局所化の比較を部分加群の外で見ると、通常の局所化の比較になる。 -/
theorem projectiveLaurentGradedLocalizationLinearEquiv_val (T : Finset ι) (d : ℤ)
    (z : projectiveGradedAway (projectiveLaurentDenominator R T)
      (fun n ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
        (d + n • (T.card : ℤ)))) :
    (projectiveLaurentGradedLocalizationLinearEquiv R T d z).val =
      projectiveLaurentLocalizationLinearEquiv R T z.val := rfl

/-- 射影空間の捻りの標準開係数図式と Laurent 単項式図式は自然同型。 -/
def projectivePolynomialTwistChartIso (d : ℤ) :
    projectiveGradedModuleChartDiagram (ι := ι)
        (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) d ≅
      projectiveLaurentGradedChartDiagram (ι := ι) R d := by
  classical
  refine NatIso.ofComponents (fun T ↦ ((projectiveLaurentGradedLocalizationLinearEquiv R T d).trans
      (projectiveLaurentGradeLinearEquiv R T d)).toModuleIso) ?_
  intro T U h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let V := fun n : ℕ ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
    (d + n • (T.card : ℤ))
  let f := projectiveLaurentDenominator R T
  have hz : z.val ∈ projectiveGradedAway f V := z.property
  obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f V
    (projectivePolynomialGrade_mul_denominator R T d) z.val).mp hz
  have hmk : z.val = LocalizedModule.mk m.val (projDenominator f n) := by
    rw [← hm, projectiveGradedFraction_apply]
  apply (projectiveLaurentGradeLinearEquiv R U d).symm.injective
  apply Subtype.ext
  let W := fun n : ℕ ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
    (d + n • (U.card : ℤ))
  let zU := projectiveGradedAwayRestriction
    (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm V W
    (projectiveGradedChart_mul_mem
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) (leOfHom h) d) z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso,
    ModuleCat.hom_ofHom, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  change (projectiveLaurentGradedLocalizationLinearEquiv R U d zU).val =
    ((projectiveLaurentGradeLinearEquiv R U d).symm
      (Finsupp.lmapDomain R R (projectiveLaurentDegreeExponentRestriction (leOfHom h) d)
        (projectiveLaurentGradeLinearEquiv R T d
          (projectiveLaurentGradedLocalizationLinearEquiv R T d z)))).val
  rw [projectiveLaurentGradedLocalizationLinearEquiv_val,
    projectiveLaurentGradeLinearEquiv_restrict,
    projectiveLaurentGradedLocalizationLinearEquiv_val]
  change projectiveLaurentLocalizationLinearEquiv R U
    (projectiveModuleAwayRestriction
      (show projectiveLaurentDenominator R T ∣ projectiveLaurentDenominator R U from
        ⟨_, (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm⟩) z.val) =
    projectiveLaurentChartRestriction R (leOfHom h)
      (projectiveLaurentLocalizationLinearEquiv R T z.val)
  rw [hmk, projectiveModuleAwayRestriction_mk
    (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm]
  exact (projectiveLaurentLocalizationLinearEquiv_restriction_mk R (leOfHom h) m.val n).symm

end Twists

end SerrePositivity.AlgebraicGeometry
