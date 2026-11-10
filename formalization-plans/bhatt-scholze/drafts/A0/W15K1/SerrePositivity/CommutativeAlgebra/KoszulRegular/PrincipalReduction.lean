module

public import SerrePositivity.CommutativeAlgebra.KoszulRegular.Powers
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# 主元剰余の Koszul 正則性

## 概要
非零因子を先に課したとき、残りの列の Koszul 複体を剰余環上で計算する。

## 方針
一元 Koszul 分解の増大を使い、残りのスカラー錐で準同型同値を保つ。

## 規約
通常の Koszul 複体を使う。

## 使われ方
BS 著者版 Lemma 2.38 の分冪表示の p 正則性。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]

private theorem koszulFunctor_preserves_quasiIso {n : ℕ} (x : Fin n → R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((koszulFunctor x).map f) := by
  induction n with
  | zero => exact ‹QuasiIso f›
  | succ n ih =>
      letI := ih (Fin.init x)
      exact DerivedCompletion.scalarConeFunctor_map_quasiIso R
        (x (Fin.last n)) ((koszulFunctor (Fin.init x)).map f)

private theorem koszulComplex_cons_eq {n : ℕ} (x : Fin n → R) (a : R) :
    koszulComplex (Fin.cons a x) = koszulComplexOn x (koszulComplex (fun _ : Fin 1 => a)) := by
  induction n with
  | zero =>
      change koszulComplex (Fin.cons a x) = koszulComplex (fun _ : Fin 1 => a)
      congr 1
      funext j
      exact Fin.cases rfl (fun t => Fin.elim0 t) j
  | succ n ih =>
      have h : Fin.cons a x = Fin.snoc (α := fun _ => R) (Fin.cons a (Fin.init x)) (x (Fin.last n)) := by
        conv_lhs => rw [← Fin.snoc_init_self x]
        exact Fin.cons_snoc_eq_snoc_cons _ _ _
      rw [h, koszulComplex_succ, Fin.init_snoc, Fin.snoc_last, ih (Fin.init x)]
      rfl

private theorem span_single_range (a : R) :
    Ideal.span (Set.range (fun _ : Fin 1 => a)) = Ideal.span {a} := by
  congr 1
  ext b
  simp

/-- 概要：a が正則で剰余上の列が Koszul 正則なら、元の列に a を加えて Koszul 正則。
方針：最初に a を課す複体から剰余への増大を残りの Koszul 関手に通し、最後に a を末尾へ移す。
規約：BS 著者版 Lemma 2.38 の mod p による検出の補助。
使われ方：分冪表示環の p 正則性。 -/
theorem isKoszulResolution_snoc_of_regular_mod {n : ℕ} (x : Fin n → R) (a : R)
    (ha : IsSMulRegular R a) {S : Type u} [CommRing S]
    (e : (R ⧸ Ideal.span {a}) ≃+* S)
    (h : IsKoszulResolution (e.toRingHom ∘ Ideal.Quotient.mk (Ideal.span {a}) ∘ x)) :
    IsKoszulResolution (Fin.snoc x a) := by
  let t : Fin 1 → R := fun _ => a
  let e' := (Ideal.quotEquivOfEq (span_single_range a)).trans e
  let β := e'.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range t)))
  have ht : IsKoszulResolution t := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn t = [a] by simp [t, List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr ha
  have hβ : IsKoszulResolution (β ∘ x) := by
    have he : β ∘ x = e.toRingHom ∘ Ideal.Quotient.mk (Ideal.span {a}) ∘ x := by
      funext i
      change e ((Ideal.quotEquivOfEq (span_single_range a))
        (Ideal.Quotient.mk _ (x i))) = _
      rw [Ideal.quotEquivOfEq_mk]
      rfl
    rwa [he]
  let e₀ : ModuleCat.of R (R ⧸ Ideal.span (Set.range t)) ≅
      (ModuleCat.restrictScalars β).obj (ModuleCat.of S S) :=
    (show (R ⧸ Ideal.span (Set.range t)) ≃ₗ[R]
        (ModuleCat.restrictScalars β).obj (ModuleCat.of S S) from
      { e'.toAddEquiv with
        map_smul' := fun b c => by
          change e' (Ideal.Quotient.mk _ b * c) = β b * e' c
          rw [map_mul]; rfl }).toModuleIso
  have hcons : IsKoszulResolution (Fin.cons a x) := by
    refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
    intro i hi
    rw [koszulComplex_cons_eq]
    let g := (koszulFunctor x).map (koszulAugmentation ht)
    haveI : QuasiIso g := koszulFunctor_preserves_quasiIso x (koszulAugmentation ht)
    haveI : IsIso (HomologicalComplex.homologyMap g i) :=
      (quasiIsoAt_iff_isIso_homologyMap g i).mp inferInstance
    let E := (HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((koszulModuleFunctor x).mapIso e₀) ≪≫ koszulModuleHomologyIso β x i
    let Z := (ModuleCat.restrictScalars β).map_isZero (hβ.isZero i hi)
    exact (Z.of_iso E).of_iso
      (asIso (HomologicalComplex.homologyMap g i))
  rw [Fin.snoc_eq_cons_rotate]
  exact hcons.perm (finRotate (n+1))

/-- 概要：列の末尾に a を加えた Koszul 複体が非零次数で完全なら、元の H⁰ 上で a は正則。
方針：写像錐の負一次ホモロジーから始まる長完全列を使う。
規約：BS 著者版 Lemma 2.38 の p 正則性の検出。
使われ方：正則列に沿う分冪表示環の p 正則性。 -/
theorem isSMulRegular_quotient_of_snoc {n : ℕ} (x : Fin n → R) (a : R)
    (h : IsKoszulResolution (Fin.snoc x a)) :
    IsSMulRegular (R ⧸ Ideal.span (Set.range x)) a := by
  let K := koszulComplex x
  have hz := h.isZero (-1) (by norm_num)
  rw [koszulComplex_succ, Fin.init_snoc, Fin.snoc_last] at hz
  have hm : Mono (HomologicalComplex.homologyMap (smulId a K) 0) :=
    (Cone.exact₁ (smulId a K) (-1) 0 (by norm_num)).mono_g (hz.eq_zero_of_src _)
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id,
    ModuleCat.mono_iff_injective] at hm
  let e := (koszulComplex_homology_zero_equiv x).some
  intro b c he
  apply e.symm.injective
  apply hm
  change a • e.symm b = a • e.symm c
  simpa only [map_smul] using congrArg e.symm he

/-- 概要：主元を加えた列と主元を反転した後の列が Koszul 正則なら、元の列も Koszul 正則。
方針：負次数のホモロジーでは主元が正則で、局所化で消える元は主元の冪で消える。
規約：BS 著者版 Lemma 2.38 の mod p と p 反転による検出。
使われ方：分冪包の表示の高次 Tor の消滅。 -/
theorem isKoszulResolution_of_snoc_and_away {n : ℕ} (x : Fin n → R) (a : R)
    (h : IsKoszulResolution (Fin.snoc x a)) {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalization.Away a S] (hS : IsKoszulResolution (algebraMap R S ∘ x)) :
    IsKoszulResolution x := by
  letI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers a)
  refine ⟨?_, koszulComplex_homology_zero_equiv _⟩
  intro i hi
  by_cases hip : 0 < i
  · exact koszulComplex_isZero_homology_of_pos _ i hip
  let K := koszulComplex x
  let M := K.homology i
  have hz := h.isZero (i-1) (by omega)
  rw [koszulComplex_succ, Fin.init_snoc, Fin.snoc_last] at hz
  have hm : Mono (HomologicalComplex.homologyMap (smulId a K) i) :=
    (Cone.exact₁ (smulId a K) (i-1) i (by omega)).mono_g (hz.eq_zero_of_src _)
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id,
    ModuleCat.mono_iff_injective] at hm
  have ha : IsSMulRegular M a := hm
  haveI := ModuleCat.isZero_iff_subsingleton.mp (hS.isZero i hi)
  let e := flatBaseChangeKoszulHomologyEquiv R S x i
  haveI : Subsingleton (S ⊗[R] M) := e.symm.injective.subsingleton
  rw [ModuleCat.isZero_iff_subsingleton]
  apply subsingleton_of_forall_eq 0
  intro m
  have hloc : (1 ⊗ₜ[R] m : S ⊗[R] M) = 0 := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
    (TensorProduct.mk R S M 1)).mp hloc
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (s : R) a).mp s.property
  apply ha.pow k
  change a ^ k • m = a ^ k • (0 : M)
  rw [hk, smul_zero]
  exact hs

end SerrePositivity
