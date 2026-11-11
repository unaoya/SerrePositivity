module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex
public import SerrePositivity.AlgebraicGeometry.CechTupleContraction
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
概要：狭義増加タプルによる Čech 複体を全タプル版と比較する。
方針：符号付き整列と成分制限を使い、制限写像付きコチェインへ整数鎖のホモトピーを移す。
規約：添字集合は全順序を持つ。係数は有限交叉の包含に沿う図式で与える。
使われ方：射影有限性を有界な複体で計算し、細分の写像には全タプル版を使う。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι]

variable {k l m : ℕ}

/-- 各生成元の像に現れるタプルの頂点が、元の頂点集合に収まること。 -/
def CechTupleMapPreservesSupport (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k) : Prop :=
  ∀ (t : Fin l → ι) (u : Fin k → ι), u ∈ (P (Finsupp.single t 1)).support →
    cechTupleSupport u ⊆ cechTupleSupport t

/-- 頂点部分集合ごとの鎖加群を保つ線形写像は、生成元の頂点集合を保つ。 -/
theorem CechTupleMapPreservesSupport.of_chainsOn
    (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k)
    (hP : ∀ (T : Set ι) (x : CechTupleChains ι l),
      x ∈ cechTupleChainsOn T l → P x ∈ cechTupleChainsOn T k) :
    CechTupleMapPreservesSupport P := by
  intro t u hu
  have hx : Finsupp.single t (1 : ℤ) ∈ cechTupleChainsOn (cechTupleSupport t : Set ι) l :=
    Finsupp.single_mem_supported ℤ 1 fun j ↦
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hy := hP _ _ hx
  have hsubset : ∀ j, u j ∈ (cechTupleSupport t : Set ι) :=
    (Finsupp.mem_supported ℤ _).mp hy hu
  intro a ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
  exact hsubset j

/-- 転置は鎖写像の和を保つ。 -/
theorem fullCechTranspose_add (D : Finset ι ⥤ ModuleCat R)
    (P Q : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k) :
    fullCechTranspose D (P + Q) = fullCechTranspose D P + fullCechTranspose D Q := by
  apply LinearMap.ext
  intro a
  funext t
  simp [fullCechTranspose]

/-- 転置は鎖写像の差を保つ。 -/
theorem fullCechTranspose_sub (D : Finset ι ⥤ ModuleCat R)
    (P Q : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k) :
    fullCechTranspose D (P - Q) = fullCechTranspose D P - fullCechTranspose D Q := by
  apply LinearMap.ext
  intro a
  funext t
  simp [fullCechTranspose]

/-- 頂点集合を保つ鎖写像の合成は、転置すると逆順になる。 -/
theorem fullCechTranspose_comp (D : Finset ι ⥤ ModuleCat R)
    (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k)
    (Q : CechTupleChains ι m →ₗ[ℤ] CechTupleChains ι l)
    (hP : CechTupleMapPreservesSupport P) (hQ : CechTupleMapPreservesSupport Q) :
    fullCechTranspose D (P.comp Q) = (fullCechTranspose D Q).comp (fullCechTranspose D P) := by
  apply LinearMap.ext
  intro a
  funext t
  let z := Q (Finsupp.single t 1)
  change fullCechEvaluateAt D k (cechTupleSupport t) (P z) a =
    fullCechEvaluateAt D l (cechTupleSupport t) z (fullCechTranspose D P a)
  have hz : ∑ u ∈ z.support, z u • Finsupp.single u 1 = z := by
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using z.sum_single
  calc
    _ = ∑ u ∈ z.support, z u •
        fullCechEvaluateAt D k (cechTupleSupport t) (P (Finsupp.single u 1)) a := by
      conv_lhs => rw [← hz]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = _ := by
      conv_rhs => unfold fullCechEvaluateAt
      rw [Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro u hu
      have hs := hQ t u hu
      simp only [dite_eq_left hs, LinearMap.comp_apply, LinearMap.proj_apply]
      change z u • fullCechEvaluateAt D k (cechTupleSupport t) (P (Finsupp.single u 1)) a =
        z u • (D.map (homOfLE hs)).hom
          (fullCechEvaluateAt D k (cechTupleSupport u) (P (Finsupp.single u 1)) a)
      exact congrArg (z u • ·)
        (fullCechEvaluateAt_restrict D hs _ (fun w hw ↦ hP u w hw) a).symm

/-- 交代境界の転置は全タプル版の余境界。 -/
theorem fullCechTranspose_boundary (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    fullCechTranspose D (cechTupleBoundary (ι := ι) k) = fullCechDifferential D k := by
  apply LinearMap.ext
  intro a
  funext t
  change fullCechEvaluateAt D k (cechTupleSupport t)
    (cechTupleBoundary k (Finsupp.single t 1)) a = fullCechDifferential D k a t
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul, map_sum,
    map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  unfold fullCechDifferential
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, fullCechEvaluateAt_single D (cechTupleSupport_face_subset t _),
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- 境界でタプルの頂点集合は増えない。 -/
theorem cechTupleBoundary_preservesSupport (k : ℕ) :
    CechTupleMapPreservesSupport (cechTupleBoundary (ι := ι) k) := by
  apply CechTupleMapPreservesSupport.of_chainsOn
  intro T x hx
  have h : cechTupleChainsOn T (k + 1) ≤ (cechTupleChainsOn T k).comap (cechTupleBoundary k) := by
    change Finsupp.supported ℤ ℤ {t : Fin (k + 1) → ι | ∀ j, t j ∈ T} ≤ _
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    change cechTupleBoundary k (Finsupp.single t 1) ∈ cechTupleChainsOn T k
    simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Finsupp.single_mem_supported ℤ 1 (fun j ↦ ht (i.succAbove j)))
  exact h hx

/--
概要：頂点集合を保つ比較ホモトピーは、制限写像付き Čech コチェイン上で同じ方程式を満たす。
方針：整数鎖のホモトピー方程式を転置し、交代境界の転置を余境界に置き換える。
規約：長さ零を含む。通常の Čech 次数では長さ一から使う。
使われ方：狭義増加版への成分制限がコホモロジーを保つことを示す。
-/
theorem fullCechTransposedHomotopy_identity (D : Finset ι ⥤ ModuleCat R)
    (P : ∀ n, CechTupleChains ι n →ₗ[ℤ] CechTupleChains ι n)
    (hP0 : P 0 = LinearMap.id)
    (hP : ∀ n (x : CechTupleChains ι (n + 1)),
      cechTupleBoundary n (P (n + 1) x) = P n (cechTupleBoundary n x))
    (hps : ∀ T n (x : CechTupleChains ι n),
      x ∈ cechTupleChainsOn T n → P n x ∈ cechTupleChainsOn T n)
    (n : ℕ) :
    (fullCechTranspose D (cechTupleComparisonHomotopy P (n + 1))).comp
        (fullCechDifferential D (n + 1)) +
      (fullCechDifferential D n).comp (fullCechTranspose D (cechTupleComparisonHomotopy P n)) =
      LinearMap.id - fullCechTranspose D (P (n + 1)) := by
  have hH (q : ℕ) : CechTupleMapPreservesSupport (cechTupleComparisonHomotopy P q) :=
    CechTupleMapPreservesSupport.of_chainsOn _ fun T x hx ↦
      cechTupleComparisonHomotopy_mem_chainsOn P hps T q x hx
  rw [← fullCechTranspose_boundary D (n + 1), ← fullCechTranspose_boundary D n,
    ← fullCechTranspose_comp D _ _ (cechTupleBoundary_preservesSupport (n + 1)) (hH (n + 1)),
    ← fullCechTranspose_comp D _ _ (hH n) (cechTupleBoundary_preservesSupport n),
    ← fullCechTranspose_add, cechTupleComparisonHomotopy_identity P hP0 hP,
    fullCechTranspose_sub, fullCechTranspose_id]

/-- 重複するタプルを零にし、単射なタプルを符号付きの増加タプルへ送る。 -/
def cechTupleSortProject (k : ℕ) : CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k := by
  classical
  exact Finsupp.linearCombination ℤ fun t ↦
    if ht : Function.Injective t then
      (cechTupleSortingPerm t ht).sign.val •
        Finsupp.single (t ∘ cechTupleSortingPerm t ht) 1
    else 0

/-- 添字の置換はタプルに現れる頂点集合を変えない。 -/
theorem cechTupleSupport_perm {k : ℕ} (t : Fin k → ι) (σ : Equiv.Perm (Fin k)) :
    cechTupleSupport (t ∘ σ) = cechTupleSupport t := by
  ext a
  simp only [cechTupleSupport, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨σ j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨σ.symm j, by simp⟩

/-- タプルの置換を整列置換の前に合成すると、元の整列置換を得る。 -/
theorem cechTupleSortingPerm_comp {k : ℕ} (t : Fin k → ι) (ht : Function.Injective t)
    (σ : Equiv.Perm (Fin k)) :
    σ * cechTupleSortingPerm (t ∘ σ) (ht.comp σ.injective) = cechTupleSortingPerm t ht := by
  have orderEmb_congr {s s' : Finset ι} (h : s = s') (hs : s.card = k) (hs' : s'.card = k) :
      s.orderEmbOfFin hs = s'.orderEmbOfFin hs' := by
    subst s'
    rfl
  apply Equiv.ext
  intro j
  apply ht
  exact (cechTupleSortingPerm_apply (t ∘ σ) (ht.comp σ.injective) j).trans
    ((congrArg (fun e : Fin k ↪o ι ↦ e j)
      (orderEmb_congr (cechTupleSupport_perm t σ) _ _)).trans
      (cechTupleSortingPerm_apply t ht j).symm)

/-- 符号付き整列の値は、元のタプルの置換の符号だけ変わる。 -/
theorem cechTupleSortProject_single_perm {k : ℕ} (t : Fin k → ι) (σ : Equiv.Perm (Fin k)) :
    cechTupleSortProject k (Finsupp.single (t ∘ σ) 1) =
      σ.sign.val • cechTupleSortProject k (Finsupp.single t 1) := by
  classical
  by_cases ht : Function.Injective t
  · have hcomp := cechTupleSortingPerm_comp t ht σ
    have hsorted : (t ∘ σ) ∘ cechTupleSortingPerm (t ∘ σ) (ht.comp σ.injective) =
        t ∘ cechTupleSortingPerm t ht := funext fun j ↦
      congrArg (fun e : Equiv.Perm (Fin k) ↦ t (e j)) hcomp
    have hperm : cechTupleSortingPerm (t ∘ σ) (ht.comp σ.injective) =
        σ⁻¹ * cechTupleSortingPerm t ht := by
      rw [← hcomp, ← mul_assoc, inv_mul_cancel, one_mul]
    have hsign := congrArg Equiv.Perm.sign hperm
    simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv] at hsign
    simp only [cechTupleSortProject, Finsupp.linearCombination_single, one_smul,
      dite_eq_left ht, dite_eq_left (ht.comp σ.injective), hsorted, hsign,
      Units.val_mul, mul_smul]
  · have h' : ¬ Function.Injective (t ∘ σ) := fun hi ↦ ht (by
      intro a b h
      have e : σ.symm a = σ.symm b := hi (by simpa using h)
      exact σ.symm.injective e)
    simp [cechTupleSortProject, ht, h']

/-- 符号付き整列は、与えられた頂点集合内のタプル鎖を保つ。 -/
theorem cechTupleSortProject_mem_chainsOn (T : Set ι) (k : ℕ) (x : CechTupleChains ι k)
    (hx : x ∈ cechTupleChainsOn T k) : cechTupleSortProject k x ∈ cechTupleChainsOn T k := by
  classical
  have hs : cechTupleChainsOn T k ≤ (cechTupleChainsOn T k).comap (cechTupleSortProject k) := by
    change Finsupp.supported ℤ ℤ {t : Fin k → ι | ∀ i, t i ∈ T} ≤ _
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    change cechTupleSortProject k (Finsupp.single t 1) ∈ cechTupleChainsOn T k
    by_cases h : Function.Injective t
    · simp only [cechTupleSortProject, Finsupp.linearCombination_single, one_smul, dite_eq_left h]
      exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℤ 1
        (fun j ↦ ht (cechTupleSortingPerm t h j)))
    · simp [cechTupleSortProject, h]
  exact hs hx

/-- 整列写像はすでに狭義増加なタプルを固定する。 -/
theorem cechTupleSortProject_single_of_strictMono (k : ℕ) (t : Fin k → ι) (ht : StrictMono t) :
    cechTupleSortProject k (Finsupp.single t 1) = Finsupp.single t 1 := by
  classical
  simp [cechTupleSortProject, ht.injective, cechTupleSortingPerm_eq_one t ht]

/-- 空タプルの生成する増大項では整列写像が恒等になる。 -/
theorem cechTupleSortProject_zero : cechTupleSortProject (ι := ι) 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t c
  have ht : StrictMono t := fun i ↦ Fin.elim0 i
  rw [← Finsupp.smul_single_one t c, map_zsmul, map_zsmul,
    cechTupleSortProject_single_of_strictMono 0 t ht, LinearMap.id_apply]

private theorem cechPermDelete_zsign {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) (i : Fin (k + 2)) :
    (-1 : ℤ) ^ i.val * (cechPermDelete σ i).sign.val =
      σ.sign.val * (-1 : ℤ) ^ (σ i).val := by
  let a : ℤˣ := (-1) ^ i.val
  let b : ℤˣ := (-1) ^ (σ i).val
  let c := (cechPermDelete σ i).sign
  have h : σ.sign * a = b * c := cechPermDelete_sign σ i
  have e : a * c = σ.sign * b := calc
    a * c = (b * b) * (a * c) := by rw [Int.units_mul_self, one_mul]
    _ = (b * a) * (b * c) := by ac_rfl
    _ = (b * a) * (σ.sign * a) := by rw [← h]
    _ = (σ.sign * b) * (a * a) := by ac_rfl
    _ = σ.sign * b := by rw [Int.units_mul_self, mul_one]
  simpa only [a, b, c, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
    congrArg Units.val e

/-- 整列した境界は、タプルの置換の符号に従って変わる。 -/
theorem cechTupleSortProject_boundary_perm {k : ℕ} (t : Fin (k + 2) → ι)
    (σ : Equiv.Perm (Fin (k + 2))) :
    cechTupleSortProject (k + 1)
      (cechTupleBoundary (k + 1) (Finsupp.single (t ∘ σ) 1)) =
    σ.sign.val • cechTupleSortProject (k + 1)
      (cechTupleBoundary (k + 1) (Finsupp.single t 1)) := by
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul, map_sum, map_zsmul,
    Finset.smul_sum]
  apply Fintype.sum_equiv σ
  intro i
  have hf : (t ∘ σ) ∘ i.succAbove =
      (t ∘ (σ i).succAbove) ∘ cechPermDelete σ i := by
    funext j
    exact congrArg t (cechPermDelete_apply σ i j).symm
  rw [hf, cechTupleSortProject_single_perm, smul_smul, smul_smul, cechPermDelete_zsign]

private theorem cechTupleSortProject_boundary_single {k : ℕ} (t : Fin (k + 1) → ι) :
    cechTupleBoundary k (cechTupleSortProject (k + 1) (Finsupp.single t 1)) =
      cechTupleSortProject k (cechTupleBoundary k (Finsupp.single t 1)) := by
  classical
  cases k with
  | zero =>
    have ht : StrictMono t := by
      intro i j h
      change Fin 1 at i j
      exact (lt_irrefl i ((Subsingleton.elim j i) ▸ h)).elim
    rw [cechTupleSortProject_single_of_strictMono _ t ht, cechTupleSortProject_zero,
      LinearMap.id_apply]
  | succ k =>
    by_cases ht : Function.Injective t
    · let σ := cechTupleSortingPerm t ht
      have hsorted : StrictMono (t ∘ σ) := by
        have e : t ∘ σ = (cechTupleSupport t).orderEmbOfFin (cechTupleSupport_card ht) :=
          funext (cechTupleSortingPerm_apply t ht)
        rw [e]
        exact OrderEmbedding.strictMono _
      have hfix : cechTupleSortProject (k + 1)
          (cechTupleBoundary (k + 1) (Finsupp.single (t ∘ σ) 1)) =
          cechTupleBoundary (k + 1) (Finsupp.single (t ∘ σ) 1) := by
        simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul,
          map_sum, map_zsmul]
        apply Finset.sum_congr rfl
        intro j _
        rw [cechTupleSortProject_single_of_strictMono _ _
          (hsorted.comp (Fin.strictMono_succAbove j))]
      have e := cechTupleSortProject_boundary_perm t σ
      rw [hfix] at e
      have hP : cechTupleSortProject (k + 2) (Finsupp.single t 1) =
          σ.sign.val • Finsupp.single (t ∘ σ) 1 := by
        simp [cechTupleSortProject, ht, σ]
      have hsquare : σ.sign.val * σ.sign.val = (1 : ℤ) := by
        exact congrArg Units.val (Int.units_mul_self σ.sign)
      rw [hP, map_zsmul, e, smul_smul, hsquare, one_smul]
    · have hpair : ∃ i j, t i = t j ∧ i ≠ j := by
        by_contra! h
        exact ht (fun i j e ↦ h i j e)
      obtain ⟨i, j, heq, hne⟩ := hpair
      let σ := Equiv.swap i j
      have hinvariant : t ∘ σ = t := by
        funext l
        by_cases hi : l = i
        · subst l
          simpa [σ] using heq.symm
        by_cases hj : l = j
        · subst l
          simpa [σ] using heq
        simp [σ, Equiv.swap_apply_of_ne_of_ne hi hj]
      have hsign : σ.sign.val = (-1 : ℤ) := by
        simp [σ, Equiv.Perm.sign_swap hne]
      have h := cechTupleSortProject_boundary_perm t σ
      rw [hinvariant, hsign, neg_one_zsmul] at h
      have hzero : cechTupleSortProject (k + 1)
          (cechTupleBoundary (k + 1) (Finsupp.single t 1)) = 0 := by
        ext u
        have hcoeff := congrArg (fun z : CechTupleChains ι (k + 1) ↦ z u) h
        simp only [Finsupp.neg_apply] at hcoeff
        simp only [Finsupp.zero_apply]
        omega
      rw [hzero]
      simp [cechTupleSortProject, ht]

/--
概要：符号付き整列は全タプルの境界と可換になる。
方針：単射なら増加列に置換する。重複があればその二位置の交換で境界の各整数係数を消す。
規約：増大項を含む。重複の場合には自由整数加群の捩れのなさを使う。
使われ方：整列と恒等写像を比較する支持付き鎖ホモトピーを得る。
-/
theorem cechTupleSortProject_boundary (k : ℕ) (x : CechTupleChains ι (k + 1)) :
    cechTupleBoundary k (cechTupleSortProject (k + 1) x) =
      cechTupleSortProject k (cechTupleBoundary k x) := by
  have h : (cechTupleBoundary (ι := ι) k).comp (cechTupleSortProject (k + 1)) =
      (cechTupleSortProject k).comp (cechTupleBoundary k) := by
    apply Finsupp.lhom_ext
    intro t c
    rw [← Finsupp.smul_single_one t c, map_zsmul, map_zsmul]
    exact congrArg (c • ·) (cechTupleSortProject_boundary_single t)
  exact LinearMap.congr_fun h x

/-- 符号付き整列の転置は、成分制限と符号付き延長の合成。 -/
theorem fullCechTranspose_sortProject (D : Finset ι ⥤ ModuleCat R) (n : ℕ) :
    fullCechTranspose D (cechTupleSortProject n) =
      (orderedCechExtendFull D n).comp (fullCechRestrictOrdered D n) := by
  classical
  apply LinearMap.ext
  intro a
  funext t
  change fullCechEvaluateAt D n (cechTupleSupport t)
      (cechTupleSortProject n (Finsupp.single t 1)) a =
    orderedCechExtendFull D n (fullCechRestrictOrdered D n a) t
  by_cases ht : Function.Injective t
  · let v := (cechTupleSupport t).orderEmbOfFin (cechTupleSupport_card ht)
    have hv : t ∘ cechTupleSortingPerm t ht = v := funext (cechTupleSortingPerm_apply t ht)
    have hs : cechTupleSupport v = cechTupleSupport t := by
      rw [← hv]
      exact cechTupleSupport_perm t _
    have e : cechTupleSortProject n (Finsupp.single t 1) =
        (cechTupleSortingPerm t ht).sign.val • Finsupp.single (v : Fin n → ι) (1 : ℤ) := by
      simp [cechTupleSortProject, ht, hv]
    rw [e, map_zsmul, LinearMap.smul_apply, fullCechEvaluateAt_single D hs.le]
    unfold orderedCechExtendFull
    rw [LinearMap.pi_apply, dite_eq_left ht, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
    rfl
  · have e : cechTupleSortProject n (Finsupp.single t 1) = 0 := by
      simp [cechTupleSortProject, ht]
    rw [e, map_zero, LinearMap.zero_apply]
    unfold orderedCechExtendFull
    rw [LinearMap.pi_apply, dite_eq_right ht, LinearMap.zero_apply]

/-- 符号付き延長は狭義増加版と全タプル版の余境界に可換。 -/
theorem orderedCechExtendFull_comp_differential (D : Finset ι ⥤ ModuleCat R) (n : ℕ) :
    (orderedCechExtendFull D (n + 1)).comp (orderedCechDifferential D n) =
      (fullCechDifferential D n).comp (orderedCechExtendFull D n) := by
  have hP (q : ℕ) : CechTupleMapPreservesSupport (cechTupleSortProject (ι := ι) q) :=
    CechTupleMapPreservesSupport.of_chainsOn _ fun T x hx ↦
      cechTupleSortProject_mem_chainsOn T q x hx
  have hchain : (cechTupleBoundary (ι := ι) n).comp (cechTupleSortProject (n + 1)) =
      (cechTupleSortProject n).comp (cechTupleBoundary n) :=
    LinearMap.ext (cechTupleSortProject_boundary n)
  have h := congrArg (fun e ↦ fullCechTranspose D e) hchain
  rw [fullCechTranspose_comp D _ _ (cechTupleBoundary_preservesSupport n) (hP (n + 1)),
    fullCechTranspose_comp D _ _ (hP n) (cechTupleBoundary_preservesSupport n),
    fullCechTranspose_sortProject, fullCechTranspose_sortProject, fullCechTranspose_boundary] at h
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := fullCechRestrictOrdered_surjective D n a
  have hcomm : fullCechRestrictOrdered D (n + 1) (fullCechDifferential D n b) =
      orderedCechDifferential D n (fullCechRestrictOrdered D n b) :=
    LinearMap.congr_fun (fullCechRestrictOrdered_comp_differential D n) b
  change orderedCechExtendFull D (n + 1)
      (orderedCechDifferential D n (fullCechRestrictOrdered D n b)) =
    fullCechDifferential D n (orderedCechExtendFull D n (fullCechRestrictOrdered D n b))
  rw [← hcomm]
  exact LinearMap.congr_fun h b

/-- 符号付き延長を狭義増加タプルに制限すると、元のコチェインを得る。 -/
theorem fullCechRestrictOrdered_extendFull (D : Finset ι ⥤ ModuleCat R) (n : ℕ) :
    (fullCechRestrictOrdered D n).comp (orderedCechExtendFull D n) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := fullCechRestrictOrdered_surjective D n a
  funext t
  have e : fullCechTranspose D (cechTupleSortProject n) b =
      orderedCechExtendFull D n (fullCechRestrictOrdered D n b) :=
    LinearMap.congr_fun (fullCechTranspose_sortProject D n) b
  change orderedCechExtendFull D n (fullCechRestrictOrdered D n b) t.val = b t.val
  rw [← e]
  change fullCechEvaluateAt D n (cechTupleSupport t.val)
    (cechTupleSortProject n (Finsupp.single t.val 1)) b = b t.val
  rw [cechTupleSortProject_single_of_strictMono n t.val t.property,
    fullCechEvaluateAt_single D le_rfl]
  change (D.map (𝟙 (cechTupleSupport t.val))).hom (b t.val) = b t.val
  rw [D.map_id]
  rfl

/-- 符号付き延長をコチェイン写像にまとめる。 -/
def orderedCechComplexExtendFull (D : Finset ι ⥤ ModuleCat R) :
    orderedCechComplex D ⟶ fullCechComplex D :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (orderedCechExtendFull D (q + 1))) (by
    intro q
    change ModuleCat.ofHom (orderedCechExtendFull D (q + 1)) ≫
        (fullCechComplex D).d q (q + 1) =
      (orderedCechComplex D).d q (q + 1) ≫ ModuleCat.ofHom (orderedCechExtendFull D (q + 2))
    simp only [orderedCechComplex, fullCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (orderedCechExtendFull_comp_differential D (q + 1)).symm)

/-- 整列と恒等写像のホモトピーのコチェイン成分。 -/
def fullCechOrderHomotopyComponent (D : Finset ι ⥤ ModuleCat R) (i j : ℕ) :
    (fullCechComplex D).X i ⟶ (fullCechComplex D).X j :=
  if e : j + 1 = i then
    eqToHom (congrArg (fullCechComplex D).X e.symm) ≫
      ModuleCat.ofHom (fullCechTranspose D
        (cechTupleComparisonHomotopy cechTupleSortProject (j + 1)))
  else 0

private theorem fullCechOrderHomotopyComponent_succ (D : Finset ι ⥤ ModuleCat R) (j : ℕ) :
    fullCechOrderHomotopyComponent D (j + 1) j =
      ModuleCat.ofHom (fullCechTranspose D
        (cechTupleComparisonHomotopy cechTupleSortProject (j + 1))) := by
  unfold fullCechOrderHomotopyComponent
  rw [dite_eq_left (rfl : j + 1 = j + 1), eqToHom_refl]
  rfl

/-- 符号付き延長と成分制限の合成を、全タプル版の恒等と比較する。 -/
def fullCechOrderHomotopy (D : Finset ι ⥤ ModuleCat R) :
    Homotopy (𝟙 (fullCechComplex D)) (fullCechComplexRestrictOrdered D ≫
      orderedCechComplexExtendFull D) where
  hom := fullCechOrderHomotopyComponent D
  zero i j h := by
    have e : ¬j + 1 = i := h
    exact dite_eq_right e
  comm i := by
    rw [Homotopy.dNext_cochainComplex, fullCechOrderHomotopyComponent_succ]
    have h := fullCechTransposedHomotopy_identity D cechTupleSortProject
      cechTupleSortProject_zero cechTupleSortProject_boundary cechTupleSortProject_mem_chainsOn i
    rw [fullCechTranspose_sortProject] at h
    cases i with
    | zero =>
      rw [Homotopy.prevD_zero_cochainComplex, add_zero]
      have hz : fullCechTranspose D
          (cechTupleComparisonHomotopy (ι := ι) cechTupleSortProject 0) = 0 := by
        apply LinearMap.ext
        intro a
        funext t
        simp [fullCechTranspose, cechTupleComparisonHomotopy]
      rw [hz, LinearMap.comp_zero, add_zero] at h
      simp only [fullCechComplex, CochainComplex.of_d, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, fullCechComplexRestrictOrdered, orderedCechComplexExtendFull,
        CochainComplex.ofHom]
      apply ModuleCat.hom_ext
      change LinearMap.id =
        (fullCechTranspose D (cechTupleComparisonHomotopy cechTupleSortProject 1)).comp
          (fullCechDifferential D 1) +
        (orderedCechExtendFull D 1).comp (fullCechRestrictOrdered D 1)
      exact (eq_sub_iff_add_eq.mp h).symm
    | succ i =>
      rw [Homotopy.prevD_succ_cochainComplex, fullCechOrderHomotopyComponent_succ]
      simp only [fullCechComplex, CochainComplex.of_d, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, fullCechComplexRestrictOrdered, orderedCechComplexExtendFull,
        CochainComplex.ofHom]
      apply ModuleCat.hom_ext
      change LinearMap.id =
        (fullCechTranspose D (cechTupleComparisonHomotopy cechTupleSortProject (i + 2))).comp
          (fullCechDifferential D (i + 2)) +
        (fullCechDifferential D (i + 1)).comp
          (fullCechTranspose D (cechTupleComparisonHomotopy cechTupleSortProject (i + 1))) +
        (orderedCechExtendFull D (i + 2)).comp (fullCechRestrictOrdered D (i + 2))
      exact (eq_sub_iff_add_eq.mp h).symm

/-- 全タプル版から狭義増加版への成分制限はホモトピー同値。 -/
def fullCechOrderedHomotopyEquiv (D : Finset ι ⥤ ModuleCat R) :
    HomotopyEquiv (fullCechComplex D) (orderedCechComplex D) where
  hom := fullCechComplexRestrictOrdered D
  inv := orderedCechComplexExtendFull D
  homotopyHomInvId := (fullCechOrderHomotopy D).symm
  homotopyInvHomId := Homotopy.ofEq (by
    ext n : 1
    apply ModuleCat.hom_ext
    exact fullCechRestrictOrdered_extendFull D (n + 1))

/-- 全タプル版と狭義増加版は各次数で同じコホモロジーを持つ。 -/
def fullCechOrderedHomologyIso (D : Finset ι ⥤ ModuleCat R) (q : ℕ) :
    (fullCechComplex D).homology q ≅ (orderedCechComplex D).homology q :=
  (fullCechOrderedHomotopyEquiv D).toHomologyIso q

end SerrePositivity.AlgebraicGeometry
