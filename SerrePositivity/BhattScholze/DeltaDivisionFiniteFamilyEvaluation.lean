module

public import SerrePositivity.BhattScholze.DeltaDivisionEvaluationFamilyStep
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteFamilyResidueKoszul
public import SerrePositivity.BhattScholze.DeltaDivisionSourceFiniteTor

/-! # 有限根族の全深さ実評価列と源グラフの座標 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {σ : Type u}

/-- 有限根族のδ座標を、深さ0から順に列挙する。 -/
def deltaDivisionFiniteFamilyCoordinates {m : ℕ} (s : Fin m → σ) : ℕ → List (σ × ℕ)
  | 0 => List.ofFn fun i => (s i, 0)
  | N + 1 => deltaDivisionFiniteFamilyCoordinates s N ++ List.ofFn fun i => (s i, N + 1)

/-- 座標列は、ちょうど選択根族の深さN以下の座標を含む。 -/
theorem deltaDivisionFiniteFamilyCoordinates_mem {m : ℕ} (s : Fin m → σ)
    (N : ℕ) (z : σ × ℕ) :
    z ∈ deltaDivisionFiniteFamilyCoordinates s N ↔
      ∃ i : Fin m, ∃ k : ℕ, k ≤ N ∧ (s i, k) = z := by
  induction N with
  | zero =>
      simp only [deltaDivisionFiniteFamilyCoordinates, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, 0, le_rfl, rfl⟩
      · rintro ⟨i, k, hk, rfl⟩
        have hk0 : k = 0 := by omega
        subst k
        exact ⟨i, rfl⟩
  | succ N ih =>
      simp only [deltaDivisionFiniteFamilyCoordinates, List.mem_append, ih, List.mem_ofFn]
      constructor
      · rintro (⟨i, k, hk, he⟩ | ⟨i, he⟩)
        · exact ⟨i, k, by omega, he⟩
        · exact ⟨i, N + 1, le_rfl, he⟩
      · rintro ⟨i, k, hk, he⟩
        by_cases h : k ≤ N
        · exact Or.inl ⟨i, k, h, he⟩
        · have heq : k = N + 1 := by omega
          subst k
          exact Or.inr ⟨i, he⟩

/-- 異なる根を選ぶと、全深さの座標列にも重複はない。 -/
theorem deltaDivisionFiniteFamilyCoordinates_nodup {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) (N : ℕ) :
    (deltaDivisionFiniteFamilyCoordinates s N).Nodup := by
  have hblock (k : ℕ) : (List.ofFn fun i => (s i, k)).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ he => hs (congrArg Prod.fst he))
  induction N with
  | zero => exact hblock 0
  | succ N ih =>
      rw [deltaDivisionFiniteFamilyCoordinates, List.nodup_append]
      refine ⟨ih, hblock _, ?_⟩
      intro z hz w hz' hzw
      subst w
      obtain ⟨i, k, hk, he⟩ := (deltaDivisionFiniteFamilyCoordinates_mem s N z).mp hz
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz'
      have h := congrArg Prod.snd (he.trans hj.symm)
      change k = N + 1 at h
      omega

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "B₀" => Ideal.span {(p : L₀), MvPolynomial.C d}
local notation "R₀" => L₀ ⧸ B₀
local notation "q₀" => Ideal.Quotient.mk B₀

/-- 同じ実座標列のδ反復関係像は、既存の全深さ実残余リスト。 -/
theorem deltaDivisionFiniteFamilyCoordinates_map_iterated {m : ℕ} (s : Fin m → σ) (N : ℕ) :
    (deltaDivisionFiniteFamilyCoordinates s N).map
      (fun z => q₀ (deltaDivisionIteratedRelation D d a z.1 z.2)) =
        deltaDivisionFiniteResidueFamilyList D d a s N := by
  induction N with
  | zero => simp only [deltaDivisionFiniteFamilyCoordinates, List.map_ofFn,
      Function.comp_def, deltaDivisionFiniteResidueFamilyList]
  | succ N ih => simp only [deltaDivisionFiniteFamilyCoordinates, List.map_append, ih,
      List.map_ofFn, Function.comp_def, deltaDivisionFiniteResidueFamilyList]

/-- 全有限座標を同じ標準剰余射で実評価したリスト。 -/
def deltaDivisionFiniteEvaluationFamilyList {m : ℕ} (s : Fin m → σ) (N : ℕ) : List R₀ :=
  (deltaDivisionFiniteFamilyCoordinates s N).map
    (fun z => q₀ (deltaDivisionEvaluationRelation D d a z.1 z.2))

/-- 実評価リストも、元の実有限δ関係イデアルの像を生成する。 -/
theorem deltaDivisionFiniteEvaluationFamilyList_ofList {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) :
    Ideal.ofList (deltaDivisionFiniteEvaluationFamilyList D d a s N) =
      (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  unfold deltaDivisionFiniteEvaluationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  simp only [deltaDivisionFiniteEvaluationFamilyList, List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨i, k, hk, rfl⟩ := (deltaDivisionFiniteFamilyCoordinates_mem s N w).mp hw
    exact ⟨(s i, ⟨k, by omega⟩), he⟩
  · rintro ⟨⟨t, k⟩, he⟩
    obtain ⟨i, rfl⟩ := hs t
    exact ⟨(s i, k.val), (deltaDivisionFiniteFamilyCoordinates_mem s N _).mpr
      ⟨i, k.val, by omega, rfl⟩, he⟩

/-- 全δ反復列が弱正則なら、同じ全深さの実評価列も弱正則。 -/
theorem deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hg : ∀ N, RingTheory.Sequence.IsWeaklyRegular R₀
      (deltaDivisionFiniteResidueFamilyList D d a s N)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀
      (deltaDivisionFiniteEvaluationFamilyList D d a s N) := by
  induction N with
  | zero =>
      simpa only [deltaDivisionFiniteEvaluationFamilyList, deltaDivisionFiniteFamilyCoordinates,
        List.map_ofFn, Function.comp_def, deltaDivisionFiniteResidueFamilyList,
        deltaDivisionEvaluationRelation, deltaDivisionIteratedRelation,
        Function.iterate_zero_apply] using hg 0
  | succ N ih =>
      have hstep : deltaDivisionFiniteEvaluationFamilyList D d a s (N + 1) =
          deltaDivisionFiniteEvaluationFamilyList D d a s N ++
            List.ofFn fun i => q₀ (deltaDivisionEvaluationRelation D d a (s i) (N + 1)) := by
        simp only [deltaDivisionFiniteEvaluationFamilyList, deltaDivisionFiniteFamilyCoordinates,
          List.map_append, List.map_ofFn, Function.comp_def]
      rw [hstep, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      have hr := hg (N + 1)
      rw [deltaDivisionFiniteResidueFamilyList,
        RingTheory.Sequence.isWeaklyRegular_append_iff] at hr
      have hIg : (Ideal.ofList (deltaDivisionFiniteResidueFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          deltaDivisionFiniteResidueFamilyList_ofList D d a s s.surjective N]
      have hIe : (Ideal.ofList (deltaDivisionFiniteEvaluationFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          deltaDivisionFiniteEvaluationFamilyList_ofList D d a s s.surjective N]
      rw [hIe]
      have hrg := hr.2
      rw [hIg] at hrg
      let J := (deltaDivisionFiniteRelationIdeal D d a N).map q₀
      let qN := (Ideal.Quotient.mk J).comp q₀
      have hkill : deltaDivisionFiniteRelationIdeal D d a N ≤ RingHom.ker qN := by
        intro z hz
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q₀ hz)
      have hrg' : RingTheory.Sequence.IsWeaklyRegular (R₀ ⧸ J)
          (List.ofFn fun i => qN (deltaDivisionIteratedRelation D d a (s i) (N + 1))) := by
        simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using
          (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mpr hrg
      have hre := deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular D d a qN N hkill s hrg'
      exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mp
        (by simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using hre)

variable {m : ℕ} (s : Fin m ≃ σ) (N : ℕ)
local notation "cs" => deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)

/-- 有限根族の全実座標に沿う評価関係は、実mod(p,d)Koszul分解を与える。 -/
theorem deltaRootFiniteResidueEvaluationFamily_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get i).1 ((cs).get i).2)) := by
  let f : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (f ∘ (cs).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) c₁ s
    (fun k => deltaRootFiniteResidueFamilyList_isWeaklyRegular D d a s hpA v hv k) N

/-- 同じ全実座標の源グラフ商のTorは、実残余評価Koszulホモロジー。 -/
def deltaRootFiniteResidueEvaluationFamilySourceTorIso (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs).length =>
        q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs).get j).1 ((cs).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs).get
      (deltaDivisionFiniteFamilyCoordinates_nodup s s.injective N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j)) =
      (fun j : Fin (cs).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get j).1 ((cs).get j).2)) := by
    funext j
    exact congrArg q₁ (deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs).get j))
  rw [he] at e
  exact e

/-- 有限根族の全深さ源グラフ商の、実残余自由δ射に沿う正次数Torは零。 -/
theorem deltaRootFiniteResidueEvaluationFamilySource_tor_subsingleton
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) := by
  have hr := deltaRootFiniteResidueEvaluationFamily_isKoszulResolution D d a s N hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaRootFiniteResidueEvaluationFamilySourceTorIso D d a s N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze
