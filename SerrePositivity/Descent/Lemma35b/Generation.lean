module

public import SerrePositivity.Descent.Lemma35b.Truncate
public import SerrePositivity.FiniteLength
public import SerrePositivity.OrdinaryEuler

/-!
# `K₀^{m}(A)` は Koszul 複体で生成される（Lemma 3.5b の共通の入力、段階 5）

`A` を Noether 局所環、`z` を `m_A` を生成する列で、Koszul 複体 `K(z)` が `A/(z) = k` の分解
（`IsKoszulResolution z`）とする。このとき、`z` に台をもつ完全 `A` 複体 `Q` には整数 `m` があって
`[Q] = m · [K(z)]`（`K0.exists_eq_zsmul_koszul`）。したがって `K₀^{m}(A)` からの準同型は
`[K(z)]` での値で決まる（`K0.hom_ext_koszul`）。

証明はホモロジーの長さの総和についての帰納法（デヴィサージュ）。シフトで最上段を `0` 次にそろえ、

- `H^0(Q) ≠ 0` なら全射 `H^0(Q) → k` を選び、`Q → k[0]` を擬同型 `K(z) → k[0]` に沿って
  持ち上げる（K 射影性）。写像錐は長さの総和が 1 小さく、`[Q] = [K(z)] - [錐]`。
- `H^0(Q) = 0` なら最上段を切り詰めて、幅の小さいホモトピー同値な複体に移る。

正則性は `IsKoszulResolution z` を通してだけ使う（正則局所環なら層 3a の A1 から出る）。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

variable {A : Type u} [CommRing A] [IsLocalRing A] {e : ℕ} {z : Fin e → A}

/-! ## 剰余体まわり -/

section residue

variable (hz : Ideal.span (Set.range z) = maximalIdeal A)

include hz in
lemma isArtinianRing_quotient_span_of_eq : IsArtinianRing (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz]
  exact inferInstanceAs (IsArtinianRing (ResidueField A))

include hz in
lemma isSimpleModule_quotient_span_of_eq : IsSimpleModule A (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz, isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)

include hz in
/-- 有限生成で `0` でない加群は `A/(z) = k` に全射をもつ。 -/
lemma exists_surjective_quotient_span (H : ModuleCat.{u} A) [Module.Finite A H]
    (hH : ¬ IsZero H) :
    ∃ ε : H ⟶ ModuleCat.of A (A ⧸ Ideal.span (Set.range z)), Function.Surjective ε.hom := by
  have : Nontrivial H := by
    rw [ModuleCat.isZero_iff_subsingleton] at hH
    exact not_subsingleton_iff_nontrivial.mp hH
  obtain h | ⟨N, hN, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule A H)
  · exact absurd h bot_ne_top
  have : IsSimpleModule A (H ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := H ⧸ N)
  let ψ := φ.trans (Submodule.quotEquivOfEq _ _ hz.symm)
  exact ⟨ModuleCat.ofHom (ψ.toLinearMap ∘ₗ N.mkQ), ψ.surjective.comp N.mkQ_surjective⟩

end residue

/-! ## Koszul 複体の添加写像 -/

section koszul

variable (hK : IsKoszulResolution z)

/-- `H^0(K(z)) ≅ A/(z)`。 -/
noncomputable def koszulH0Iso :
    (koszulComplex z).homology 0 ≅ ModuleCat.of A (A ⧸ Ideal.span (Set.range z)) :=
  hK.equiv.some.toModuleIso

omit [IsLocalRing A] in
lemma koszulComplex_d_zero_one : (koszulComplex z).d 0 1 = 0 :=
  (koszulComplex_isZero_X_of_pos z 1 one_pos).eq_of_tgt _ _

/-- 添加写像 `K(z) → (A/(z))[0]`。 -/
noncomputable def koszulAugmentation :
    koszulComplex z ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range z))) :=
  toSingleOfHomology (koszulComplex z) (koszulComplex_d_zero_one) (koszulH0Iso hK).hom

instance quasiIso_koszulAugmentation : QuasiIso (koszulAugmentation hK) :=
  quasiIso_toSingleOfHomology _ _ _ hK.isZero

include hK in
/-- `χ_A(K(z)) = length_A(A/(z)) = 1`（`z` が `m_A` を生成するとき）。 -/
theorem chiOrd_koszulComplex (hz : Ideal.span (Set.range z) = maximalIdeal A) :
    chiOrd (koszulComplex z) = 1 := by
  unfold chiOrd
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul,
      (koszulH0Iso hK).toLinearEquiv.length_eq]
    have := isSimpleModule_quotient_span_of_eq hz
    rw [Module.length_eq_one A _]
    simp
  · intro i hi
    have := ModuleCat.subsingleton_of_isZero (hK.isZero i hi)
    simp [Module.length_eq_zero]

end koszul

/-! ## 生成 -/

variable [IsNoetherianRing A] (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hK : IsKoszulResolution z)

include hz in
/-- 台つき完全複体のホモロジーは有限長。 -/
lemma length_homology_ne_top (Q : PerfSupp A z) (i : ℤ) :
    Module.length A (Q.1.homology i) ≠ ⊤ := by
  have := isArtinianRing_quotient_span_of_eq hz
  exact Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i)

include hz hK in
/-- 錐による一歩：最上段が `0` 次で `H^0(Q) ≠ 0` なら、`Q → K(z)` で
錐の長さの総和が 1 小さいものがある。 -/
lemma exists_mappingCone_step (Q : PerfSupp A z) (htop : ∀ i : ℤ, 0 < i → IsZero (Q.1.X i))
    (h0 : ¬ IsZero (Q.1.homology 0)) :
    ∃ (f : Q.1 ⟶ (koszulPerfSupp z).1),
      homologyLengthSum (CochainComplex.mappingCone f) + 1 = homologyLengthSum Q.1 := by
  have hQd : Q.1.d 0 1 = 0 := (htop 1 one_pos).eq_of_tgt _ _
  have := Q.2.finite 0
  have : Module.Finite A (Q.1.homology 0) := homology_moduleFinite Q.1 0
  obtain ⟨ε, hε⟩ := exists_surjective_quotient_span hz _ h0
  have : ∀ n, Projective (Q.1.X n) := fun n ↦ projective_of_free (Q.2.free n)
  have : Q.1.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact htop
  have : Q.1.IsKProjective := CochainComplex.isKProjective_of_projective Q.1 0
  obtain ⟨f, ⟨H⟩⟩ :=
    exists_lift_of_quasiIso (koszulAugmentation hK) (toSingleOfHomology Q.1 hQd ε)
  have hf0 : HomologicalComplex.homologyMap f 0 = ε ≫ (koszulH0Iso hK).inv := by
    have h1 := toSingleOfHomology_homologyMap Q.1 hQd ε
    have h2 := toSingleOfHomology_homologyMap (koszulComplex z) koszulComplex_d_zero_one
      (koszulH0Iso hK).hom
    have h2' : HomologicalComplex.homologyMap (koszulAugmentation hK) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso _ 0 _).hom = (koszulH0Iso hK).hom := h2
    rw [← h1, ← H.homologyMap_eq, HomologicalComplex.homologyMap_comp]
    simp only [Category.assoc]
    rw [reassoc_of% h2', Iso.hom_inv_id, Category.comp_id]
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap f 0).hom := by
    rw [hf0]
    intro y
    obtain ⟨x, hx⟩ := hε ((koszulH0Iso hK).hom y)
    exact ⟨x, by simp [hx]⟩
  have hK0 : Module.length A ((koszulComplex z).homology 0) = 1 := by
    rw [(koszulH0Iso hK).toLinearEquiv.length_eq]
    have := isSimpleModule_quotient_span_of_eq hz
    exact Module.length_eq_one A _
  exact ⟨f, homologyLengthSum_mappingCone f htop (fun i hi ↦ hK.isZero i hi) hsurj hK0
    (length_homology_ne_top hz Q) Q.2.bounded⟩

include hz hK in
/-- **`K₀^{m}(A)` は `[K(z)]` で生成される**。 -/
theorem K0.exists_eq_zsmul_koszul (Q : PerfSupp A z) :
    ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) := by
  suffices H : ∀ n (Q : PerfSupp A z), homologyLengthSum Q.1 = n →
      ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) from H _ Q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- 最上段が `0` 次、最下段が `-w` 次以上の場合
  have norm : ∀ (w : ℕ) (Q : PerfSupp A z), homologyLengthSum Q.1 = n →
      (∀ i : ℤ, 0 < i → IsZero (Q.1.X i)) → (∀ i : ℤ, i < -(w : ℤ) → IsZero (Q.1.X i)) →
      ∃ m : ℤ, K0.mk Q = m • K0.mk (koszulPerfSupp z) := by
    intro w
    induction w with
    | zero => ?_
    | succ w ihw => ?_
    all_goals
      intro Q hn htop hbot
      by_cases h0 : IsZero (Q.1.homology 0)
      swap
      · -- 錐による一歩
        obtain ⟨f, hlen⟩ := exists_mappingCone_step hz hK Q htop h0
        have hc := Q.2.mappingCone f (koszulPerfSupp z).2
        obtain ⟨m, hm⟩ := ih (homologyLengthSum (CochainComplex.mappingCone f)) (by omega)
          ⟨_, hc⟩ rfl
        have hcone := K0.mk_cone Q (koszulPerfSupp z) f hc
        refine ⟨1 - m, ?_⟩
        rw [sub_smul, one_smul, ← hm, hcone, sub_sub_cancel]
      -- 最上段の切り詰め
      obtain ⟨Q', hfree, hfin, htop', hbot', ⟨E⟩⟩ :=
        exists_homotopyEquiv_truncate Q.1 Q.2.free Q.2.finite htop h0
      have hQ' : IsPerfectSupported z Q' :=
        { bounded := by
            obtain ⟨a, b, hab⟩ := Q.2.bounded
            refine ⟨min a (-1), 0, fun i hi ↦ ?_⟩
            rcases hi with hi | hi
            · exact hbot' i (by omega) (hab i (Or.inl (by omega)))
            · exact htop' i (by omega)
          free := hfree
          finite := hfin
          supported := Q.2.supported.of_homotopyEquiv E.symm }
      have hmk : K0.mk Q = K0.mk ⟨Q', hQ'⟩ := (K0.mk_eq_of_homotopyEquiv ⟨Q', hQ'⟩ Q E).symm
      have hlen : homologyLengthSum Q' = n := by
        rw [homologyLengthSum_eq_of_homotopyEquiv E, hn]
    -- `w = 0`：`Q'` は零
    · refine ⟨0, ?_⟩
      rw [zero_smul, hmk]
      refine K0.mk_eq_zero_of_isZero _ (isZero_of_isZero_X fun i ↦ ?_)
      rcases lt_or_ge (-1) i with hi | hi
      · exact htop' i hi
      · exact hbot' i hi (hbot i (by omega))
    -- `w + 1`：`Q'⟦-1⟧` に帰納法の仮定を使う
    · obtain ⟨m, hm⟩ := ihw ⟨Q'⟦(-1 : ℤ)⟧, hQ'.shift (-1)⟩
        (by rw [homologyLengthSum_shift, hlen])
        (fun i hi ↦ htop' (i + -1) (by omega))
        (fun i hi ↦ hbot' (i + -1) (by omega) (hbot _ (by push_cast at hi ⊢; omega)))
      rw [K0.mk_shift ⟨Q', hQ'⟩ (-1), Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg,
        Units.val_one, neg_smul, one_smul] at hm
      refine ⟨-m, ?_⟩
      rw [hmk, neg_smul, ← hm, neg_neg]
  -- 一般の `Q`：シフトで最上段を `0` 次にそろえる
  intro Q hn
  obtain ⟨a, b, hab⟩ := Q.2.bounded
  obtain ⟨m, hm⟩ := norm (b - a).toNat ⟨Q.1⟦b⟧, Q.2.shift b⟩
    (by rw [homologyLengthSum_shift, hn])
    (fun i hi ↦ hab (i + b) (by omega))
    (fun i hi ↦ hab (i + b) (by omega))
  rw [K0.mk_shift] at hm
  refine ⟨((b.negOnePow : ℤˣ) : ℤ) * m, ?_⟩
  rw [mul_smul, ← hm, ← mul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

include hz hK in
/-- `K₀^{m}(A)` からの準同型は `[K(z)]` での値で決まる。 -/
theorem K0.hom_ext_koszul {β : Type*} [AddCommGroup β] {φ ψ : K0Supported A z →+ β}
    (h : φ (K0.mk (koszulPerfSupp z)) = ψ (K0.mk (koszulPerfSupp z))) : φ = ψ :=
  K0.hom_ext fun Q ↦ by
    obtain ⟨m, hm⟩ := K0.exists_eq_zsmul_koszul hz hK Q
    rw [hm, map_zsmul, map_zsmul, h]

end SerrePositivity
