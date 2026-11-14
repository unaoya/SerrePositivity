module

public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.HomologicalAlgebra.FlatKoszulFiniteness
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation

/-!
# Koszul 正則列の冪

## 概要
Koszul 正則性は各元を正の冪に置き換えても保たれる（BS 著者版 Lemma 2.38 の証明）。

## 方針
最後の元については写像錐の長完全列を用いる。順序は多項式環上の Tor の比較で移す。

## 規約
Koszul 正則性は正次数のホモロジーの消滅。係数環は任意。

## 使われ方
分冪代数の mod p の計算。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]

private theorem cone_smul_homologyMap
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : R) (i : ℤ) :
    HomologicalComplex.homologyMap (smulId a K) i = a • 𝟙 (K.homology i) := by
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]

private theorem mono_smul_pow {M : ModuleCat.{u} R} {a : R}
    (h : Mono (a • 𝟙 M)) (k : ℕ) : Mono (a ^ k • 𝟙 M) := by
  rw [ModuleCat.mono_iff_injective] at h ⊢
  change Function.Injective (fun x : M => a • x) at h
  change Function.Injective (fun x : M => a ^ k • x)
  induction k with
  | zero =>
      intro x y hxy
      simpa only [pow_zero, one_smul] using hxy
  | succ k ih =>
      intro x y hxy
      simp only [pow_succ', mul_smul] at hxy
      exact ih (h hxy)

private theorem epi_smul_pow {M : ModuleCat.{u} R} {a : R}
    (h : Epi (a • 𝟙 M)) (k : ℕ) : Epi (a ^ k • 𝟙 M) := by
  rw [ModuleCat.epi_iff_surjective] at h ⊢
  change Function.Surjective (fun x : M => a • x) at h
  change Function.Surjective (fun x : M => a ^ k • x)
  induction k with
  | zero =>
      intro z
      exact ⟨z, by simp⟩
  | succ k ih =>
      intro z
      obtain ⟨y, hy⟩ := h z
      obtain ⟨x, hx⟩ := ih y
      refine ⟨x, ?_⟩
      change a ^ (k + 1) • x = z
      rw [pow_succ', mul_smul]
      exact (congrArg (fun v : M => a • v) hx).trans hy

/-- 概要：Koszul 正則列の最後の元を冪で置き換えても Koszul 正則。
方針：元の写像錐のホモロジーが消える次数では、隣接するスカラー射の全射性と単射性が冪にも移る。
規約：係数環に Noether 性を要求しない（BS 著者版 Lemma 2.38 の証明）。
使われ方：各座標の冪への置換。 -/
theorem isKoszulResolution_snoc_pow {n : ℕ} (x : Fin (n+1) → R)
    (h : IsKoszulResolution x) (k : ℕ) :
    IsKoszulResolution (Fin.snoc (Fin.init x) (x (Fin.last n) ^ k)) := by
  let K := koszulComplex (Fin.init x)
  let a := x (Fin.last n)
  let y := Fin.snoc (Fin.init x) (a ^ k)
  refine ⟨?_, koszulComplex_homology_zero_equiv y⟩
  intro i hi
  have hz := h.isZero i hi
  change IsZero ((Cone.cone (smulId a K)).homology i) at hz
  have hE : Epi (HomologicalComplex.homologyMap (smulId a K) i) :=
    (Cone.exact₂ (smulId a K) i).epi_f (hz.eq_zero_of_tgt _)
  have hM : Mono (HomologicalComplex.homologyMap (smulId a K) (i+1)) :=
    (Cone.exact₁ (smulId a K) i (i+1) rfl).mono_g (hz.eq_zero_of_src _)
  rw [cone_smul_homologyMap] at hE hM
  have hE' : Epi (HomologicalComplex.homologyMap (smulId (a ^ k) K) i) := by
    rw [cone_smul_homologyMap]
    exact epi_smul_pow hE k
  have hM' : Mono (HomologicalComplex.homologyMap (smulId (a ^ k) K) (i+1)) := by
    rw [cone_smul_homologyMap]
    exact mono_smul_pow hM k
  let f := smulId (a ^ k) K
  have hι : HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i = 0 :=
    zero_of_epi_comp _ (comp_eq_zero_transport (Cone.S₂ f i) _ _ _ _ _
      (Cone.e_naturality i f) (Cone.e_naturality i (CochainComplex.mappingCone.inr f)))
  have hδ : Cone.δ f i (i+1) rfl = 0 :=
    zero_of_comp_mono _ (comp_eq_zero_transport (Cone.S₁ f i (i+1) rfl) _ _ _ _ _
      (Cone.δ_square f i (i+1) rfl) (Cone.e_naturality (i+1) f))
  have hzero : IsZero ((Cone.cone f).homology i) := by
    have hmono : Mono (Cone.δ f i (i+1) rfl) := (Cone.exact₃ f i (i+1) rfl).mono_g hι
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ f i (i+1) rfl),
      Category.id_comp, zero_comp, hδ]
  change IsZero ((Cone.cone (smulId (y (Fin.last n)) (koszulComplex (Fin.init y)))).homology i)
  rw [show Fin.init y = Fin.init x from Fin.init_snoc (a ^ k) (Fin.init x),
    show y (Fin.last n) = a ^ k from Fin.snoc_last _ _]
  exact hzero


private theorem polynomialVariables_isKoszulResolution {n : ℕ} (e : Equiv.Perm (Fin n)) :
    IsKoszulResolution (fun i => (MvPolynomial.X (e i) : MvPolynomial (Fin n) R)) := by
  simpa only [BhattScholze.Andre.monicRelation, Polynomial.eval₂_X] using
    (BhattScholze.Andre.monicRelation_fin_isKoszulResolution
      (fun _ : Fin n => (Polynomial.X : Polynomial R)) (fun _ => Polynomial.monic_X)
      e e.injective)

/-- 概要：環同型に沿って Koszul 正則性を引き戻す。
方針：係数を制限した Koszul 複体と元の複体のホモロジーを比較する。
規約：BS 著者版 Lemma 2.38 の剰余表示の補助。
使われ方：自由座標の剰余 Koszul 正則性。 -/
theorem isKoszulResolution_of_ringEquiv {S : Type u} [CommRing S] (e : R ≃+* S)
    {n : ℕ} {x : Fin n → R} (h : IsKoszulResolution (e.toRingHom ∘ x)) :
    IsKoszulResolution x := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let e₀ : ModuleCat.of R R ≅ F.obj (ModuleCat.of S S) :=
    (show R ≃ₗ[R] F.obj (ModuleCat.of S S) from
      { e.toAddEquiv with
        map_smul' := fun r s => by
          change e (r*s) = e r * e s
          exact map_mul e r s }).toModuleIso
  refine ⟨?_, koszulComplex_homology_zero_equiv x⟩
  intro i hi
  have e₁ : ((koszulModuleFunctor x).obj (ModuleCat.of R R)).homology i ≅
      F.obj ((koszulComplex (e.toRingHom ∘ x)).homology i) :=
    (HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((koszulModuleFunctor x).mapIso e₀) ≪≫ koszulModuleHomologyIso e.toRingHom x i
  have h₁ := (F.map_isZero (h.isZero i hi)).of_iso e₁
  rwa [koszulModuleFunctor_self_eq] at h₁

/-- 概要：Koszul 正則列を並べ替えても Koszul 正則。
方針：各順序の複体を、多項式環で全変数を殺した商との同じ Tor に比較する。
規約：係数環は任意（BS 著者版 Lemma 2.38 の証明の補助）。
使われ方：任意の座標を冪に置き換える。 -/
theorem IsKoszulResolution.perm {n : ℕ} {x : Fin n → R} (h : IsKoszulResolution x)
    (e : Equiv.Perm (Fin n)) : IsKoszulResolution (x ∘ e) := by
  let P := MvPolynomial (Fin n) R
  let φ : P →+* R := (MvPolynomial.aeval x).toRingHom
  letI : Algebra P R := φ.toAlgebra
  let v : Fin n → P := MvPolynomial.X
  have h₁ : algebraMap P R ∘ (v ∘ e) = x ∘ e := by
    funext i
    exact MvPolynomial.aeval_X x (e i)
  have h₂ : algebraMap P R ∘ v = x := by
    funext i
    exact MvPolynomial.aeval_X x i
  have hv : Set.range (v ∘ e) = Set.range v := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, congrArg v (e.apply_symm_apply i)⟩
  refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
  intro i hi
  by_cases hip : 0 < i
  · exact koszulComplex_isZero_homology_of_pos _ i hip
  have hn : i = -(i.natAbs : ℤ) := by omega
  have hcomp₁ := algebraKoszulTorComparison (C := R) (v ∘ e)
    (polynomialVariables_isKoszulResolution e) i.natAbs
  have hcomp₂ := algebraKoszulTorComparison (C := R) v
    (polynomialVariables_isKoszulResolution (Equiv.refl _)) i.natAbs
  rw [h₁, hv, ← hn] at hcomp₁
  rw [h₂, ← hn] at hcomp₂
  have hz := ModuleCat.isZero_iff_subsingleton.mp (h.isZero i hi)
  rw [ModuleCat.isZero_iff_subsingleton]
  letI : Subsingleton ((ModuleCat.restrictScalars (algebraMap P R)).obj
    ((koszulComplex x).homology i)) := hz
  exact (hcomp₁.symm ≪≫ hcomp₂).toLinearEquiv.injective.subsingleton

/-- 概要：Koszul 正則列の各元を任意の冪に置き換えても Koszul 正則。
方針：冪にする座標を最後に移し、写像錐の計算を適用して元の順序に戻す。
規約：零乗では商が零環になる（BS 著者版 Lemma 2.38 の証明）。
使われ方：mod p で各正則元の p 乗を使う分冪計算。 -/
theorem IsKoszulResolution.pow {n : ℕ} {x : Fin n → R} (h : IsKoszulResolution x)
    (m : Fin n → ℕ) : IsKoszulResolution (fun i => x i ^ m i) := by
  classical
  cases n with
  | zero => exact isKoszulResolution_zero _
  | succ n =>
      have hs : ∀ (S : Finset (Fin (n+1))),
          IsKoszulResolution (fun i => if i ∈ S then x i ^ m i else x i) := by
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using h
        | @insert i S hi ih =>
            let v := fun j => if j ∈ S then x j ^ m j else x j
            let e := Equiv.swap i (Fin.last n)
            have hp := isKoszulResolution_snoc_pow (v ∘ e) (ih.perm e) (m i)
            have hw := hp.perm e.symm
            convert hw using 1
            funext j
            by_cases hj : j = i
            · subst j
              simp [v, e, hi, Function.comp_def, Equiv.symm_swap]
            · have hj' : e.symm j ≠ Fin.last n := by
                intro hh
                apply hj
                calc
                  j = e (e.symm j) := (e.apply_symm_apply j).symm
                  _ = i := by rw [hh]; simp [e]
              obtain ⟨t, ht⟩ := Fin.eq_castSucc_of_ne_last hj'
              have ht' : e t.castSucc = j :=
                (congrArg e ht).trans (e.apply_symm_apply j)
              simp only [Finset.mem_insert, hj, false_or]
              change v j = Fin.snoc (Fin.init (v ∘ e)) _ (e.symm j)
              rw [← ht, Fin.snoc_castSucc]
              change v j = v (e t.castSucc)
              rw [ht']
      simpa using hs Finset.univ

end SerrePositivity
