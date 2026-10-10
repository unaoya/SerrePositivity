module

public import SerrePositivity.CategoryTheory.ScalarZeroCone
public import SerrePositivity.CategoryTheory.ConeLengthBinomial
public import SerrePositivity.CommutativeAlgebra.PowTorsionCategory
public import SerrePositivity.PerfectComplex.NormalizedEuler

/-! # 無限分解にも適用できる Koszul ホモロジー長の二項公式

各スカラーが零ホモトピックなら、各段の錐の長完全列は短完全列になる。
複体の有界性・射影性は不要であり、長さの定義域と各次数での有限性だけを使う。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 零スカラーの Koszul 構成は、他の消去スカラーを指数を増やさずに保つ。 -/
lemma koszulComplexOn_smul_zero {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, x j • 𝟙 ((homotopyQuot R).obj P) = 0)
    (a : R) (ha : a • 𝟙 ((homotopyQuot R).obj P) = 0) :
    a • 𝟙 ((homotopyQuot R).obj (koszulComplexOn x P)) = 0 := by
  induction e generalizing a with
  | zero => exact ha
  | succ e ih =>
    let Q := koszulComplexOn (Fin.init x) P
    let T := CochainComplex.mappingCone.triangleh (smulId (x (Fin.last e)) Q)
    have hc := ih (Fin.init x) (fun j ↦ hx j.castSucc) (x (Fin.last e)) (hx (Fin.last e))
    have ha' := ih (Fin.init x) (fun j ↦ hx j.castSucc) a ha
    have hf : T.mor₁ = 0 := by
      change (homotopyQuot R).map (x (Fin.last e) • 𝟙 Q) = 0
      simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hc
    exact scalar_zero_on_zero_cone T (Cone.triangleh_distinguished _) hf a ha' ha'

variable {J : Ideal R} (lam : NormalizedLength R J)

/-- 零ホモトピックな射の錐では、冪ねじれ性と長さの加法性が得られる。 -/
lemma lambdaHomology_null_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hf : Homotopy f 0) (q : ℤ)
    (hQ : IsPowTorsion J (Q.homology q)) (hP : IsPowTorsion J (P.homology (q + 1))) :
    IsPowTorsion J ((Cone.cone f).homology q) ∧
      lam.len ((Cone.cone f).homology q) =
        lam.len (Q.homology q) + lam.len (P.homology (q + 1)) := by
  have hz (i : ℤ) : HomologicalComplex.homologyMap f i = 0 := by
    simpa only [HomologicalComplex.homologyMap_zero] using hf.homologyMap_eq i
  let S := ShortComplex.mk _ _
    (comp_eq_zero_transport (Cone.S₃ f q (q + 1) rfl)
      (Cone.e q Q) (Cone.e q (Cone.cone f)) (Cone.e (q + 1) P)
      _ (Cone.δ f q (q + 1) rfl)
      (Cone.e_naturality q (CochainComplex.mappingCone.inr f)) (Cone.δ_square f q (q + 1) rfl))
  have : Mono S.f := (Cone.exact₂ f q).mono_g (hz q)
  have : Epi S.g := (Cone.exact₁ f q (q + 1) rfl).epi_f (hz (q + 1))
  have hs : S.ShortExact := ⟨Cone.exact₃ f q (q + 1) rfl⟩
  have ht : IsPowTorsion J ((Cone.cone f).homology q) :=
    (powTorsionModule J).prop_X₂_of_shortExact hs hQ hP
  exact ⟨ht, lam.len_add_of_exact _ _ _ S.f.hom S.g.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    (LinearMap.exact_iff.mpr hs.exact.moduleCat_range_eq_ker.symm) ht⟩

/-- Koszul 構成後も長さは有限で、その実数値は錐の係数作用素で計算される。 -/
lemma lambdaHomology_koszul_null_pow {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) :
    (∀ q, IsPowTorsion J ((koszulComplexOn x P).homology q)) ∧
    (∀ q, lam.len ((koszulComplexOn x P).homology q) ≠ ⊤) ∧
    ∀ q, (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ((cochainLengthShift + 1) ^ e) (fun q ↦ (lam.len (P.homology q)).toReal) q := by
  induction e with
  | zero => exact ⟨ht, hfin, fun _ ↦ rfl⟩
  | succ e ih =>
    obtain ⟨ht', hfin', he⟩ := ih (Fin.init x) (fun j ↦ hx j.castSucc)
    have hn : Nonempty (Homotopy
        (smulId (x (Fin.last e)) (koszulComplexOn (Fin.init x) P)) 0) :=
      (nonempty_homotopy_smul_id_zero_iff _ _).mpr
        (koszulComplexOn_smul_zero (Fin.init x) P
          (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ _).mp (hx j.castSucc))
          (x (Fin.last e)) ((nonempty_homotopy_smul_id_zero_iff _ _).mp (hx (Fin.last e))))
    have hc (q : ℤ) := lambdaHomology_null_cone lam _ hn.some q (ht' q) (ht' (q + 1))
    refine ⟨fun q ↦ (hc q).1, fun q ↦ ?_, fun q ↦ ?_⟩
    · change lam.len ((Cone.cone _).homology q) ≠ ⊤
      rw [(hc q).2]
      exact ENNReal.add_ne_top.mpr ⟨hfin' q, hfin' (q + 1)⟩
    · change (lam.len ((Cone.cone _).homology q)).toReal = _
      rw [(hc q).2, ENNReal.toReal_add (hfin' q) (hfin' (q + 1)), he q, he (q + 1),
        pow_succ', Module.End.mul_apply]
      simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
        Pi.add_apply, add_comm]

/-- 零ホモトピックなスカラーの Koszul ホモロジー長の二項係数公式。 -/
theorem lambdaHomology_koszul_null_binomial {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) (q : ℤ) :
    (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) * (lam.len (P.homology (q + j))).toReal := by
  rw [(lambdaHomology_koszul_null_pow lam x P hx ht hfin).2.2 q, coneLength_binomial]

end SerrePositivity
