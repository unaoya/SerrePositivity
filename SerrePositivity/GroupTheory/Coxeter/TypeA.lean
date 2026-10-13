module

public import Mathlib.GroupTheory.Coxeter.Inversion
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign

/-!
# 型 A Coxeter 群から対称群への標準写像

ArxivFormalization の `Coxeter/TypeA.lean` から移植した一般の群論。
元コミット: `761bc6bc1b8f18764afa9f2d439264e79da14a31`。
出典・移植差分・将来の統合方針は同じディレクトリの `README.md` に記録する。

型 `Aₙ` の単純反射を `Fin (n+1)` 上の隣接互換へ送り、Coxeter 関係の検証と全射性を示す。
末尾挿入 normal form を構成し、標準準同型の単射性まで証明する。

## Main results

- `adjacentTransposition_isLiftable`: 隣接互換による型 A Coxeter 関係の検証。
- `typeAHom_simple`: 標準準同型の生成元上の値。
- `typeAHom_surjective`: 隣接互換による生成から従う全射性。
- `typeANormalForm`, `typeANormalForm_spec`: 挿入ソートによる標準語とその実現性。
- `typeANormalForm_mul_simple`: 標準語の単純生成元右乗法に関する閉性。
- `typeAHom_injective`: 型 A normal form による標準準同型の単射性。

## Implementation

- `typeANormalForm` は末尾の逆像で置換を一意に分解する挿入ソート語である。
- `typeANormalForm_mul_simple` は二次・遠方可換・braid の四場合を再帰的に処理する。
- `typeAHom_injective` は正規形が `typeAHom` の左逆を与えることから従う。

この normal-form サブツリーだけを発注粒度へ展開する rolling wave であり、同型構成より下流は
粗い粒度を保つ。
-/

@[expose] public section

namespace SerrePositivity.Coxeter

open Function Set

/-- 型 A の単純反射に対応する `Fin (n+1)` 上の隣接互換。 -/
noncomputable def adjacentTransposition {n : ℕ} (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

/-- 隣接互換は型 `Aₙ` の Coxeter 関係を満たす。

対角では位数二、隣接添字では積の位数三、非隣接添字では可換性を点ごとに検証する。 -/
theorem adjacentTransposition_isLiftable (n : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A n) (@adjacentTransposition n) := by
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp [adjacentTransposition]
  rw [ite_eq_right hij]
  by_cases hadj : (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j
  · rw [ite_eq_left hadj]
    rcases hadj with hji | hij
    · have hsucc : j.succ = i.castSucc := Fin.ext hji
      ext x
      simp [adjacentTransposition, hsucc, Equiv.swap_apply_def, pow_succ]
      grind
    · have hsucc : i.succ = j.castSucc := Fin.ext hij
      ext x
      simp [adjacentTransposition, hsucc, Equiv.swap_apply_def, pow_succ]
      grind
  · rw [ite_eq_right hadj]
    ext x
    simp [adjacentTransposition, Equiv.swap_apply_def, pow_succ]
    grind

/-- 型 `Aₙ` Coxeter 群から `Fin (n+1)` 上の対称群への標準準同型。 -/
noncomputable def typeAHom (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨@adjacentTransposition n, adjacentTransposition_isLiftable n⟩

/-- 型 A の標準準同型は単純反射を対応する隣接互換へ送る。 -/
@[simp]
theorem typeAHom_simple (n : ℕ) (i : Fin n) :
    typeAHom n ((CoxeterMatrix.A n).simple i) = adjacentTransposition i := by
  exact CoxeterSystem.lift_apply_simple _ _ _

/-- 型 A の標準準同型は全射である。

Proved by `Equiv.Perm.mclosure_swap_castSucc_succ` and closure induction. -/
theorem typeAHom_surjective (n : ℕ) : Function.Surjective (typeAHom n) := by
  intro σ
  have hσ : σ ∈ Submonoid.closure (Set.range (@adjacentTransposition n)) := by
    rw [show (@adjacentTransposition n) =
      (fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) from rfl,
      Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem σ hσ =>
      rcases hσ with ⟨i, rfl⟩
      exact ⟨(CoxeterMatrix.A n).simple i, typeAHom_simple n i⟩
  | one => exact ⟨1, map_one (typeAHom n)⟩
  | mul σ τ _ _ hσ hτ =>
      rcases hσ with ⟨x, rfl⟩
      rcases hτ with ⟨y, rfl⟩
      exact ⟨x * y, map_mul (typeAHom n) x y⟩

/-- 型 A の末尾挿入で位置 `k` を末尾まで送る降順の単純反射語。 -/
def bubbleWord : (n : ℕ) → Fin (n + 1) → List (Fin n)
  | 0, _ => []
  | n + 1, k =>
      Fin.lastCases []
        (fun k' => Fin.last n :: (bubbleWord n k').map Fin.castSucc) k

/-- 末尾位置に対応する bubble 語は空語である。 -/
@[simp] theorem bubbleWord_last (n : ℕ) : bubbleWord n (Fin.last n) = [] := by
  cases n <;> simp [bubbleWord]

/-- 非末尾位置の bubble 語は最大生成元を先頭に付ける再帰式を満たす。 -/
@[simp] theorem bubbleWord_castSucc (n : ℕ) (k : Fin (n + 1)) :
    bubbleWord (n + 1) k.castSucc =
      Fin.last n :: (bubbleWord n k).map Fin.castSucc := by
  simp [bubbleWord]

/-- `Fin n` と `Fin (n+1)` の末尾以外の部分との標準同値。 -/
noncomputable def initEquiv (n : ℕ) :
    Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} :=
  Fin.castSuccEmb.toEquivRange |>.trans <|
    Equiv.subtypeEquivRight fun x => by
      change x ∈ Set.range Fin.castSucc ↔ x ≠ Fin.last n
      rw [Fin.range_castSucc]
      change x < Fin.last n ↔ x ≠ Fin.last n
      exact Fin.lt_last_iff_ne_last

/-- `initEquiv` の値は `Fin.castSucc` である。 -/
@[simp] theorem initEquiv_apply (n : ℕ) (i : Fin n) :
    ((initEquiv n i : {x : Fin (n + 1) // x ≠ Fin.last n}) : Fin (n + 1)) = i.castSucc := by
  rfl

/-- 末尾を固定して `Perm (Fin n)` を `Perm (Fin (n+1))` へ持ち上げる準同型。 -/
noncomputable def permLift (n : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.extendDomainHom (initEquiv n)

/-- 持ち上げた置換の `castSucc` 上の値。 -/
@[simp] theorem permLift_apply_castSucc (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permLift n σ i.castSucc = (σ i).castSucc := by
  simpa [permLift] using Equiv.Perm.extendDomain_apply_image σ (initEquiv n) i

/-- 持ち上げた置換は末尾を固定する。 -/
@[simp] theorem permLift_apply_last (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permLift n σ (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

/-- 末尾を固定する置換を `Perm (Fin n)` へ制限する。 -/
noncomputable def permRestrict (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) : Equiv.Perm (Fin n) :=
  (initEquiv n).symm.permCongr
    (σ.subtypePerm fun x => by
      constructor
      · intro hx hxl
        exact hx (hxl ▸ hσ)
      · intro hx hxl
        apply hx
        exact σ.injective (hxl.trans hσ.symm))

/-- 末尾固定置換の制限は `castSucc` 上で元の置換と一致する。 -/
@[simp] theorem permRestrict_apply_castSucc (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) (i : Fin n) :
    (permRestrict n σ hσ i).castSucc = σ i.castSucc := by
  simp only [permRestrict, ne_eq, Equiv.permCongr_def, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.Perm.subtypePerm_apply, initEquiv_apply]
  rw [← initEquiv_apply n ((initEquiv n).symm ⟨σ i.castSucc, by
      intro hi
      have hi' : i.castSucc = Fin.last n := σ.injective (hi.trans hσ.symm)
      exact (Fin.castSucc_lt_last i).ne hi'⟩),
    Equiv.apply_symm_apply]

/-- 末尾固定置換を制限して再び持ち上げると元に戻る。 -/
theorem permLift_restrict (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (hσ : σ (Fin.last n) = Fin.last n) : permLift n (permRestrict n σ hσ) = σ := by
  ext x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · simp [hσ]
  · simp

/-- bubble 語が対称群上で表す置換。 -/
noncomputable def bubblePerm (n : ℕ) (k : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  typeAHom n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (bubbleWord n k))

/-- 末尾位置の bubble 置換は恒等置換である。 -/
@[simp] theorem bubblePerm_last (n : ℕ) : bubblePerm n (Fin.last n) = 1 := by
  simp [bubblePerm]

/-- `typeAHom` の `toCoxeterSystem.simple` 版の計算補題。 -/
@[simp] theorem typeAHom_toCoxeterSystem_simple (n : ℕ) (i : Fin n) :
    typeAHom n ((CoxeterMatrix.A n).toCoxeterSystem.simple i) = adjacentTransposition i := by
  exact typeAHom_simple n i

/-- 置換の持ち上げは隣接互換を添字の `castSucc` へ送る。 -/
@[simp] theorem permLift_adjacent (n : ℕ) (i : Fin n) :
    permLift (n + 1) (adjacentTransposition i) = adjacentTransposition i.castSucc := by
  ext x
  refine Fin.lastCases ?_ (fun j => ?_) x
  · rw [permLift_apply_last]
    have h₁ : Fin.last (n + 1) ≠ i.castSucc.castSucc :=
      (Fin.castSucc_lt_last i.castSucc).ne'
    have h₂ : Fin.last (n + 1) ≠ i.castSucc.succ :=
      (Fin.castSucc_lt_last i.succ).ne'
    simp [adjacentTransposition, Equiv.swap_apply_def, h₁, h₂]
  · simp [adjacentTransposition, Equiv.swap_apply_def]
    grind

/-- `castSucc` した語の標準写像は置換の持ち上げと可換する。 -/
theorem typeAHom_wordProd_map_castSucc (n : ℕ) (ω : List (Fin n)) :
    typeAHom (n + 1) ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.wordProd
      (ω.map Fin.castSucc)) =
      permLift (n + 1)
        (typeAHom n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd ω)) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
      simp only [List.map_cons, CoxeterSystem.wordProd_cons, map_mul, ih]
      congr 1
      change typeAHom (n + 1) ((CoxeterMatrix.A (n + 1)).simple i.castSucc) =
        permLift (n + 1) (typeAHom n ((CoxeterMatrix.A n).simple i))
      rw [typeAHom_simple, typeAHom_simple, permLift_adjacent]

/-- bubble 置換の非末尾位置での再帰式。 -/
@[simp] theorem bubblePerm_castSucc (n : ℕ) (k : Fin (n + 1)) :
    bubblePerm (n + 1) k.castSucc =
      adjacentTransposition (Fin.last n) * permLift (n + 1) (bubblePerm n k) := by
  rw [bubblePerm, bubbleWord_castSucc, CoxeterSystem.wordProd_cons, map_mul]
  change adjacentTransposition (Fin.last n) *
      typeAHom (n + 1) ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.wordProd
        ((bubbleWord n k).map Fin.castSucc)) = _
  rw [typeAHom_wordProd_map_castSucc]
  rfl

/-- bubble 置換は指定位置 `k` を末尾へ送る。 -/
@[simp] theorem bubblePerm_apply_self (n : ℕ) (k : Fin (n + 1)) :
    bubblePerm n k k = Fin.last n := by
  induction n with
  | zero => exact Fin.ext (by simp)
  | succ n ih =>
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp
      · rw [bubblePerm_castSucc, Equiv.Perm.mul_apply, permLift_apply_castSucc, ih]
        simp [adjacentTransposition]

/-- 任意の `Fin (n+1)` 上の置換は、末尾固定部分と一つの bubble 置換へ一意に分解される。 -/
theorem perm_decomposition_exists_unique (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    ∃! d : Fin (n + 1) × Equiv.Perm (Fin n),
      σ = permLift n d.2 * bubblePerm n d.1 := by
  let k : Fin (n + 1) := σ⁻¹ (Fin.last n)
  have hbk : (bubblePerm n k)⁻¹ (Fin.last n) = k := by
    apply (bubblePerm n k).injective
    simp [bubblePerm_apply_self]
  have hfix : (σ * (bubblePerm n k)⁻¹) (Fin.last n) = Fin.last n := by
    rw [Equiv.Perm.mul_apply, hbk]
    simp [k]
  let τ := permRestrict n (σ * (bubblePerm n k)⁻¹) hfix
  refine ⟨(k, τ), ?_, ?_⟩
  · dsimp only
    rw [permLift_restrict]
    simp
  · rintro ⟨k', τ'⟩ hdecomp
    have hk_image : σ k' = Fin.last n := by
      rw [hdecomp, Equiv.Perm.mul_apply, bubblePerm_apply_self, permLift_apply_last]
    have hk' : k' = k := by
      apply σ.injective
      rw [hk_image]
      simp [k]
    subst k'
    congr 1
    apply Equiv.Perm.extendDomainHom_injective (initEquiv n)
    change permLift n τ' = permLift n τ
    apply mul_right_cancel (b := bubblePerm n k)
    rw [← hdecomp]
    dsimp only [τ]
    rw [permLift_restrict]
    simp

/-- 型 A 正規形で用いる一意な末尾分解。 -/
noncomputable def permDecomposition (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) × Equiv.Perm (Fin n) :=
  Classical.choose (perm_decomposition_exists_unique n σ)

/-- `permDecomposition` が与える末尾分解の等式。 -/
theorem permDecomposition_spec (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    σ = permLift n (permDecomposition n σ).2 * bubblePerm n (permDecomposition n σ).1 :=
  (Classical.choose_spec (perm_decomposition_exists_unique n σ)).1

/-- 末尾分解を満たす対は `permDecomposition` に一致する。 -/
theorem permDecomposition_eq_of_spec (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (d : Fin (n + 1) × Equiv.Perm (Fin n))
    (hd : σ = permLift n d.2 * bubblePerm n d.1) : permDecomposition n σ = d := by
  exact ((Classical.choose_spec (perm_decomposition_exists_unique n σ)).2 d hd).symm

/-- 恒等置換の末尾分解は末尾位置と恒等置換からなる。 -/
@[simp] theorem permDecomposition_one (n : ℕ) :
    permDecomposition n 1 = (Fin.last n, 1) := by
  apply permDecomposition_eq_of_spec
  simp

/-- `Fin (n+1)` の置換へ割り当てる型 A の挿入ソート標準語。

構成は末尾 `n` の像を隣接互換で所定位置まで bubble し、残る `Fin n` 上の置換へ再帰する。
各段で使う交代列を連結することで、空語を恒等置換へ送る canonical な語を得る。 -/
noncomputable def typeANormalForm : (n : ℕ) → Equiv.Perm (Fin (n + 1)) → List (Fin n)
  | 0, _ => []
  | n + 1, σ =>
      (typeANormalForm n (permDecomposition (n + 1) σ).2).map Fin.castSucc ++
        bubbleWord (n + 1) (permDecomposition (n + 1) σ).1

/-- 恒等置換の型 A 正規形は空語である。 -/
@[simp] theorem typeANormalForm_one (n : ℕ) : typeANormalForm n 1 = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [typeANormalForm, ih]

/-- 型 A 正規形を標準準同型で評価すると元の置換を得る。 -/
theorem typeANormalForm_realizes (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    typeAHom n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n σ)) = σ := by
  induction n with
  | zero =>
      have hσ : σ = 1 := by
        ext x
        omega
      rw [hσ]
      simp [typeANormalForm]
  | succ n ih =>
      rw [typeANormalForm, CoxeterSystem.wordProd_append, map_mul,
        typeAHom_wordProd_map_castSucc, ih, ← bubblePerm]
      exact (permDecomposition_spec (n + 1) σ).symm

/-- 挿入ソート標準語は恒等置換で空語となり、標準準同型の下で元の置換を実現する。

証明は `n` に関する帰納法。末尾を動かす隣接互換列の積を `typeAHom_simple` で計算し、残余の
`Fin n` 上の置換には帰納仮定を適用する。 -/
theorem typeANormalForm_spec (n : ℕ) :
    typeANormalForm n 1 = [] ∧
      ∀ σ : Equiv.Perm (Fin (n + 1)),
        typeAHom n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd
          (typeANormalForm n σ)) = σ := by
  exact ⟨typeANormalForm_one n, typeANormalForm_realizes n⟩

/-- 型 A で二つの添字が一つ以上離れていれば対応する単純反射は可換する。 -/
theorem simple_comm_of_far (n : ℕ) (i j : Fin n) (h : (i : ℕ) + 1 < j) :
    (CoxeterMatrix.A n).toCoxeterSystem.simple i *
        (CoxeterMatrix.A n).toCoxeterSystem.simple j =
      (CoxeterMatrix.A n).toCoxeterSystem.simple j *
        (CoxeterMatrix.A n).toCoxeterSystem.simple i := by
  have hbraid := (CoxeterMatrix.A n).toCoxeterSystem.wordProd_braidWord_eq i j
  have hij : i ≠ j := by omega
  have hadj : ¬ ((j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j) := by omega
  have hadj' : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by omega
  have hm : CoxeterMatrix.A n i j = 2 := by
    simp [CoxeterMatrix.A, hij, hadj]
  have hm' : CoxeterMatrix.A n j i = 2 := by
    simp [CoxeterMatrix.A, hij.symm, hadj']
  change (CoxeterMatrix.A n).toCoxeterSystem.wordProd
      (CoxeterSystem.alternatingWord i j (CoxeterMatrix.A n i j)) =
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd
      (CoxeterSystem.alternatingWord j i (CoxeterMatrix.A n j i)) at hbraid
  rw [hm, hm'] at hbraid
  simpa [CoxeterSystem.alternatingWord, CoxeterSystem.wordProd_cons] using hbraid

/-- 型 A の隣接する単純反射が長さ三の braid 関係を満たす。 -/
theorem simple_braid_adjacent (n : ℕ) (i j : Fin n) (h : (i : ℕ) + 1 = j) :
    (CoxeterMatrix.A n).toCoxeterSystem.simple i *
          (CoxeterMatrix.A n).toCoxeterSystem.simple j *
        (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.simple j *
          (CoxeterMatrix.A n).toCoxeterSystem.simple i *
        (CoxeterMatrix.A n).toCoxeterSystem.simple j := by
  have hbraid := (CoxeterMatrix.A n).toCoxeterSystem.wordProd_braidWord_eq i j
  have hij : i ≠ j := by omega
  have hm : CoxeterMatrix.A n i j = 3 := by
    simp [CoxeterMatrix.A, hij, h]
  have hm' : CoxeterMatrix.A n j i = 3 := by
    simp [CoxeterMatrix.A, hij.symm, h]
  change (CoxeterMatrix.A n).toCoxeterSystem.wordProd
      (CoxeterSystem.alternatingWord i j (CoxeterMatrix.A n i j)) =
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd
      (CoxeterSystem.alternatingWord j i (CoxeterMatrix.A n j i)) at hbraid
  rw [hm, hm'] at hbraid
  simpa [CoxeterSystem.alternatingWord, CoxeterSystem.wordProd_cons, mul_assoc] using hbraid.symm

/-- 型 A の添字を `castSucc` する単純反射族は Coxeter 関係を保つ。 -/
theorem castSucc_isLiftable (n : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A n)
      (fun i : Fin n => (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i.castSucc) := by
  intro i j
  have hrel := (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_mul_simple_pow
    i.castSucc j.castSucc
  have hm : CoxeterMatrix.A n i j =
      CoxeterMatrix.A (n + 1) i.castSucc j.castSucc := by
    simp only [CoxeterMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.castSucc,
      Fin.val_castAdd]
  rw [hm]
  exact hrel

/-- 型 `Aₙ` Coxeter 群を型 `Aₙ₊₁` へ標準的に持ち上げる準同型。 -/
noncomputable def groupLift (n : ℕ) :
    (CoxeterMatrix.A n).Group →* (CoxeterMatrix.A (n + 1)).Group :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨fun i => (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i.castSucc,
      castSucc_isLiftable n⟩

/-- Coxeter 群の持ち上げは単純反射を `castSucc` へ送る。 -/
@[simp] theorem groupLift_simple (n : ℕ) (i : Fin n) :
    groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.simple i) =
      (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i.castSucc := by
  exact CoxeterSystem.lift_apply_simple _ _ _

/-- `castSucc` した語の積は Coxeter 群の持ち上げと可換する。 -/
theorem wordProd_map_castSucc (n : ℕ) (ω : List (Fin n)) :
    (CoxeterMatrix.A (n + 1)).toCoxeterSystem.wordProd (ω.map Fin.castSucc) =
      groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
      rw [List.map_cons, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
        map_mul, ih]
      congr 1

/-- bubble 語が型 A Coxeter 群で表す元。 -/
def bubbleGroup (n : ℕ) (k : Fin (n + 1)) : (CoxeterMatrix.A n).Group :=
  (CoxeterMatrix.A n).toCoxeterSystem.wordProd (bubbleWord n k)

/-- 末尾位置の bubble 群元は単位元である。 -/
@[simp] theorem bubbleGroup_last (n : ℕ) : bubbleGroup n (Fin.last n) = 1 := by
  simp [bubbleGroup]

/-- bubble 群元の非末尾位置での再帰式。 -/
@[simp] theorem bubbleGroup_castSucc (n : ℕ) (k : Fin (n + 1)) :
    bubbleGroup (n + 1) k.castSucc =
      (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple (Fin.last n) *
        groupLift n (bubbleGroup n k) := by
  rw [bubbleGroup, bubbleWord_castSucc, CoxeterSystem.wordProd_cons,
    wordProd_map_castSucc]
  rfl

/-- `castSucc.succ` 位置での bubble 語の再帰式。 -/
@[simp] theorem bubbleWord_succ_castSucc (n : ℕ) (j : Fin n) :
    bubbleWord (n + 1) j.castSucc.succ =
      Fin.last n :: (bubbleWord n j.succ).map Fin.castSucc := by
  convert bubbleWord_castSucc n j.succ using 1
  exact congrArg (bubbleWord (n + 1)) (Fin.ext rfl)

/-- 隣り合う二つの bubble 語は末尾への一文字追加で結ばれる。 -/
theorem bubbleWord_concat (n : ℕ) (i : Fin n) :
    bubbleWord n i.castSucc = (bubbleWord n i.succ).concat i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [bubbleWord]
      · rw [bubbleWord_castSucc, bubbleWord_succ_castSucc]
        simp [ih]

/-- bubble 群元を一段延ばす等式。 -/
theorem bubbleGroup_step (n : ℕ) (i : Fin n) :
    bubbleGroup n i.succ * (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      bubbleGroup n i.castSucc := by
  change (CoxeterMatrix.A n).toCoxeterSystem.wordProd (bubbleWord n i.succ) *
      (CoxeterMatrix.A n).toCoxeterSystem.simple i =
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd (bubbleWord n i.castSucc)
  rw [bubbleWord_concat, CoxeterSystem.wordProd_concat]

/-- bubble 語の末尾に同じ単純反射を掛けると二次関係で一段短くなる。 -/
theorem bubbleGroup_cancel (n : ℕ) (i : Fin n) :
    bubbleGroup n i.castSucc * (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      bubbleGroup n i.succ := by
  rw [← bubbleGroup_step]
  exact (CoxeterMatrix.A n).toCoxeterSystem.simple_mul_simple_cancel_right i

/-- bubble 語に現れる添字は開始位置以上である。 -/
theorem bubbleWord_mem_le (n : ℕ) (k : Fin (n + 1)) {j : Fin n}
    (hj : j ∈ bubbleWord n k) : (k : ℕ) ≤ j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.lastCases (motive := fun k => ∀ {j : Fin (n + 1)},
        j ∈ bubbleWord (n + 1) k → (k : ℕ) ≤ j) ?_ (fun k' => ?_) k hj
      · intro j hj
        simp at hj
      · intro j hj
        rw [bubbleWord_castSucc] at hj
        simp only [List.mem_cons, List.mem_map] at hj
        rcases hj with hj | ⟨j', hj', hj⟩
        · subst j
          change (k' : ℕ) ≤ n
          omega
        · subst j
          simpa using ih k' hj'

/-- 語の全添字が `i` より十分上なら、その語の積は `sᵢ` と可換する。 -/
theorem wordProd_comm_simple (n : ℕ) (i : Fin n) (ω : List (Fin n))
    (hω : ∀ j ∈ ω, (i : ℕ) + 1 < j) :
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω *
        (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.simple i *
        (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
      rw [CoxeterSystem.wordProd_cons]
      have hj : (i : ℕ) + 1 < j := hω j (by simp)
      have htail : ∀ k ∈ ω, (i : ℕ) + 1 < k := by
        intro k hk
        exact hω k (by simp [hk])
      calc
        ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) *
            (CoxeterMatrix.A n).toCoxeterSystem.simple i =
          (CoxeterMatrix.A n).toCoxeterSystem.simple j *
            ((CoxeterMatrix.A n).toCoxeterSystem.wordProd ω *
              (CoxeterMatrix.A n).toCoxeterSystem.simple i) := by simp [mul_assoc]
        _ = (CoxeterMatrix.A n).toCoxeterSystem.simple j *
            ((CoxeterMatrix.A n).toCoxeterSystem.simple i *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) := by rw [ih htail]
        _ = ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.simple i) *
            (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by simp [mul_assoc]
        _ = ((CoxeterMatrix.A n).toCoxeterSystem.simple i *
              (CoxeterMatrix.A n).toCoxeterSystem.simple j) *
            (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by
              rw [simple_comm_of_far n i j hj]
        _ = (CoxeterMatrix.A n).toCoxeterSystem.simple i *
            ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) := by simp [mul_assoc]

/-- bubble ブロックは十分下にある単純反射と可換する。 -/
theorem bubbleGroup_comm_simple (n : ℕ) (i : Fin n) (k : Fin (n + 1))
    (hik : (i : ℕ) + 1 < k) :
    bubbleGroup n k * (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.simple i * bubbleGroup n k := by
  apply wordProd_comm_simple
  intro j hj
  exact lt_of_lt_of_le hik (bubbleWord_mem_le n k hj)

/-- 語の全添字が `i` より十分下なら、その語の積は `sᵢ` と可換する。 -/
theorem wordProd_comm_simple_below (n : ℕ) (i : Fin n) (ω : List (Fin n))
    (hω : ∀ j ∈ ω, (j : ℕ) + 1 < i) :
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω *
        (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.simple i *
        (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
      rw [CoxeterSystem.wordProd_cons]
      have hj : (j : ℕ) + 1 < i := hω j (by simp)
      have htail : ∀ k ∈ ω, (k : ℕ) + 1 < i := by
        intro k hk
        exact hω k (by simp [hk])
      calc
        ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) *
            (CoxeterMatrix.A n).toCoxeterSystem.simple i =
          (CoxeterMatrix.A n).toCoxeterSystem.simple j *
            ((CoxeterMatrix.A n).toCoxeterSystem.wordProd ω *
              (CoxeterMatrix.A n).toCoxeterSystem.simple i) := by simp [mul_assoc]
        _ = (CoxeterMatrix.A n).toCoxeterSystem.simple j *
            ((CoxeterMatrix.A n).toCoxeterSystem.simple i *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) := by rw [ih htail]
        _ = ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.simple i) *
            (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by simp [mul_assoc]
        _ = ((CoxeterMatrix.A n).toCoxeterSystem.simple i *
              (CoxeterMatrix.A n).toCoxeterSystem.simple j) *
            (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω := by
              rw [simple_comm_of_far n j i hj]
        _ = (CoxeterMatrix.A n).toCoxeterSystem.simple i *
            ((CoxeterMatrix.A n).toCoxeterSystem.simple j *
              (CoxeterMatrix.A n).toCoxeterSystem.wordProd ω) := by simp [mul_assoc]

/-- bubble ブロックの右から境界より上の単純反射を通す braid スライド補題。 -/
theorem bubbleGroup_slide (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1))
    (hki : (k : ℕ) < i) :
    ∃ j : Fin n, j.succ = i ∧
      bubbleGroup (n + 1) k *
          (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i =
        (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple j.castSucc *
          bubbleGroup (n + 1) k := by
  induction n with
  | zero => omega
  | succ n ih =>
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.val_last] at hki
        omega
      | cast k' =>
        induction i using Fin.lastCases with
        | last =>
          induction k' using Fin.lastCases with
          | last =>
            change n + 1 < n + 1 at hki
            omega
          | cast q =>
            refine ⟨Fin.last n, by ext; simp, ?_⟩
            let T : (CoxeterMatrix.A (n + 2)).Group :=
              groupLift (n + 1) (groupLift n (bubbleGroup n q))
            have hT : T * (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) =
                (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) * T := by
              have hcomm := wordProd_comm_simple_below (n + 2) (Fin.last (n + 1))
                ((bubbleWord n q).map Fin.castSucc |>.map Fin.castSucc) (by
                  intro j hj
                  simp only [List.mem_map] at hj
                  rcases hj with ⟨j', ⟨j'', hj'', rfl⟩, rfl⟩
                  change (j'' : ℕ) + 1 < n + 1
                  omega)
              simpa only [wordProd_map_castSucc, bubbleGroup, T] using hcomm
            rw [bubbleGroup_castSucc, bubbleGroup_castSucc, map_mul, groupLift_simple]
            change ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc * T)) *
                (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) = _
            calc
              _ = (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                  ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc *
                    (T * (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple
                      (Fin.last (n + 1)))) := by simp [mul_assoc]
              _ = (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                  ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc *
                    ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple
                      (Fin.last (n + 1)) * T)) := by rw [hT]
              _ = (((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc) *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1))) * T := by
                      simp [mul_assoc]
              _ = (((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1))) *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc) *
                      T := by
                      rw [simple_braid_adjacent (n + 2) (Fin.last n).castSucc
                        (Fin.last (n + 1)) (by simp)]
              _ = (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last n).castSucc *
                  ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                    ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple
                      (Fin.last n).castSucc * T)) := by
                      simp [mul_assoc]
        | cast i' =>
          have hki' : (k' : ℕ) < i' := by
            exact hki
          obtain ⟨j, hji, hslide⟩ := ih k' i' hki'
          refine ⟨j.castSucc, ?_, ?_⟩
          · apply Fin.ext
            simpa using congrArg Fin.val hji
          · rw [bubbleGroup_castSucc]
            change ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                groupLift (n + 1) (bubbleGroup (n + 1) k')) *
                (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple i'.castSucc = _
            rw [mul_assoc, ← groupLift_simple (n + 1) i', ← map_mul, hslide,
              map_mul, groupLift_simple]
            calc
              _ = ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1)) *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple j.castSucc.castSucc) *
                  groupLift (n + 1) (bubbleGroup (n + 1) k') := by simp [mul_assoc]
              _ = ((CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple j.castSucc.castSucc *
                    (CoxeterMatrix.A (n + 2)).toCoxeterSystem.simple (Fin.last (n + 1))) *
                  groupLift (n + 1) (bubbleGroup (n + 1) k') := by
                    rw [simple_comm_of_far (n + 2) j.castSucc.castSucc
                      (Fin.last (n + 1)) (by change (j : ℕ) + 1 < n + 1; omega)]
              _ = _ := by simp [mul_assoc]

/-- Coxeter 群と置換群の持ち上げは `typeAHom` と可換する。 -/
theorem typeAHom_groupLift (n : ℕ) (x : (CoxeterMatrix.A n).Group) :
    typeAHom (n + 1) (groupLift n x) = permLift (n + 1) (typeAHom n x) := by
  change ((typeAHom (n + 1)).comp (groupLift n)) x =
    ((permLift (n + 1)).comp (typeAHom n)) x
  congr 1
  apply (CoxeterMatrix.A n).toCoxeterSystem.ext_simple
  intro i
  change typeAHom (n + 1) (groupLift n ((CoxeterMatrix.A n).simple i)) =
    permLift (n + 1) (typeAHom n ((CoxeterMatrix.A n).simple i))
  rw [show groupLift n ((CoxeterMatrix.A n).simple i) =
      (CoxeterMatrix.A (n + 1)).simple i.castSucc from groupLift_simple n i,
    typeAHom_simple, typeAHom_simple, permLift_adjacent]

/-- 対称群上の bubble ブロックを一段延ばす等式。 -/
theorem bubblePerm_step (n : ℕ) (i : Fin n) :
    bubblePerm n i.succ * adjacentTransposition i = bubblePerm n i.castSucc := by
  have h := congrArg (typeAHom n) (bubbleGroup_step n i)
  rw [map_mul] at h
  change bubblePerm n i.succ * typeAHom n ((CoxeterMatrix.A n).simple i) =
    bubblePerm n i.castSucc at h
  rw [typeAHom_simple] at h
  exact h

/-- 対称群上の bubble ブロックの二次関係による短縮。 -/
theorem bubblePerm_cancel (n : ℕ) (i : Fin n) :
    bubblePerm n i.castSucc * adjacentTransposition i = bubblePerm n i.succ := by
  have h := congrArg (typeAHom n) (bubbleGroup_cancel n i)
  rw [map_mul] at h
  change bubblePerm n i.castSucc * typeAHom n ((CoxeterMatrix.A n).simple i) =
    bubblePerm n i.succ at h
  rw [typeAHom_simple] at h
  exact h

/-- 対称群上の bubble ブロックは十分下の隣接互換と可換する。 -/
theorem bubblePerm_comm (n : ℕ) (i : Fin n) (k : Fin (n + 1))
    (hik : (i : ℕ) + 1 < k) :
    bubblePerm n k * adjacentTransposition i = adjacentTransposition i * bubblePerm n k := by
  have h := congrArg (typeAHom n) (bubbleGroup_comm_simple n i k hik)
  rw [map_mul, map_mul] at h
  change bubblePerm n k * typeAHom n ((CoxeterMatrix.A n).simple i) =
    typeAHom n ((CoxeterMatrix.A n).simple i) * bubblePerm n k at h
  rw [typeAHom_simple] at h
  exact h

/-- 対称群上の bubble ブロックの境界を横切る braid スライド。 -/
theorem bubblePerm_slide (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1))
    (hki : (k : ℕ) < i) :
    ∃ j : Fin n, j.succ = i ∧
      bubblePerm (n + 1) k * adjacentTransposition i =
        adjacentTransposition j.castSucc * bubblePerm (n + 1) k := by
  obtain ⟨j, hji, hslide⟩ := bubbleGroup_slide n k i hki
  refine ⟨j, hji, ?_⟩
  have h := congrArg (typeAHom (n + 1)) hslide
  rw [map_mul, map_mul] at h
  change bubblePerm (n + 1) k *
      typeAHom (n + 1) ((CoxeterMatrix.A (n + 1)).simple i) =
    typeAHom (n + 1) ((CoxeterMatrix.A (n + 1)).simple j.castSucc) *
      bubblePerm (n + 1) k at h
  rw [typeAHom_simple, typeAHom_simple] at h
  exact h

/-- 一段上の型 A 正規形の積を末尾固定部分と bubble 部分へ分解する。 -/
theorem typeANormalForm_prod_succ (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    (CoxeterMatrix.A (n + 1)).toCoxeterSystem.wordProd (typeANormalForm (n + 1) σ) =
      groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd
        (typeANormalForm n (permDecomposition (n + 1) σ).2)) *
      bubbleGroup (n + 1) (permDecomposition (n + 1) σ).1 := by
  rw [typeANormalForm, CoxeterSystem.wordProd_append, wordProd_map_castSucc]
  rfl

/-- 型 A 正規形が単純生成元の右乗法で閉じることの再帰的本体。 -/
theorem typeANormalForm_mul_simple_aux (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n σ) *
        (CoxeterMatrix.A n).toCoxeterSystem.simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.wordProd
        (typeANormalForm n (σ * adjacentTransposition i)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      let k := (permDecomposition (n + 1) σ).1
      let τ := (permDecomposition (n + 1) σ).2
      have hd : permDecomposition (n + 1) σ = (k, τ) := rfl
      have hσ : σ = permLift (n + 1) τ * bubblePerm (n + 1) k := by
        simpa [hd] using permDecomposition_spec (n + 1) σ
      rw [typeANormalForm_prod_succ, hd]
      by_cases hcancel : k = i.castSucc
      · have hnew : permDecomposition (n + 1) (σ * adjacentTransposition i) =
            (i.succ, τ) := by
          apply permDecomposition_eq_of_spec
          calc
            σ * adjacentTransposition i =
                (permLift (n + 1) τ * bubblePerm (n + 1) k) *
                  adjacentTransposition i := by rw [hσ]
            _ = permLift (n + 1) τ *
                  (bubblePerm (n + 1) k * adjacentTransposition i) := by simp [mul_assoc]
            _ = permLift (n + 1) τ * bubblePerm (n + 1) i.succ := by
                  rw [hcancel, bubblePerm_cancel]
        rw [typeANormalForm_prod_succ, hnew]
        calc
          (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                bubbleGroup (n + 1) k) *
              (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i =
            groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
              (bubbleGroup (n + 1) k *
                (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i) := by simp [mul_assoc]
          _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
              bubbleGroup (n + 1) i.succ := by rw [hcancel, bubbleGroup_cancel]
      · by_cases hstep : k = i.succ
        · have hnew : permDecomposition (n + 1) (σ * adjacentTransposition i) =
              (i.castSucc, τ) := by
            apply permDecomposition_eq_of_spec
            calc
              σ * adjacentTransposition i =
                  (permLift (n + 1) τ * bubblePerm (n + 1) k) *
                    adjacentTransposition i := by rw [hσ]
              _ = permLift (n + 1) τ *
                    (bubblePerm (n + 1) k * adjacentTransposition i) := by simp [mul_assoc]
              _ = permLift (n + 1) τ * bubblePerm (n + 1) i.castSucc := by
                    rw [hstep, bubblePerm_step]
          rw [typeANormalForm_prod_succ, hnew]
          calc
            (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  bubbleGroup (n + 1) k) *
                (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i =
              groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                (bubbleGroup (n + 1) k *
                  (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i) := by simp [mul_assoc]
            _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                bubbleGroup (n + 1) i.castSucc := by rw [hstep, bubbleGroup_step]
        · by_cases hbelow : (k : ℕ) < i
          · obtain ⟨j, hji, hgslide⟩ := bubbleGroup_slide n k i hbelow
            obtain ⟨j', hji', hpslide⟩ := bubblePerm_slide n k i hbelow
            have hj : j' = j := by
              apply Fin.succ_injective
              exact hji'.trans hji.symm
            subst j'
            have hnew : permDecomposition (n + 1) (σ * adjacentTransposition i) =
                  (k, τ * adjacentTransposition j) := by
              apply permDecomposition_eq_of_spec
              calc
                σ * adjacentTransposition i =
                    (permLift (n + 1) τ * bubblePerm (n + 1) k) *
                      adjacentTransposition i := by rw [hσ]
                _ = permLift (n + 1) τ *
                      (bubblePerm (n + 1) k * adjacentTransposition i) := by simp [mul_assoc]
                _ = permLift (n + 1) τ *
                      (adjacentTransposition j.castSucc * bubblePerm (n + 1) k) := by
                        rw [hpslide]
                _ = permLift (n + 1) τ *
                      (permLift (n + 1) (adjacentTransposition j) * bubblePerm (n + 1) k) := by
                        rw [permLift_adjacent]
                _ = permLift (n + 1) (τ * adjacentTransposition j) *
                      bubblePerm (n + 1) k := by rw [map_mul]; simp [mul_assoc]
            rw [typeANormalForm_prod_succ, hnew]
            calc
              (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                    bubbleGroup (n + 1) k) *
                  (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i =
                groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  (bubbleGroup (n + 1) k *
                    (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i) := by simp [mul_assoc]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple j.castSucc *
                    bubbleGroup (n + 1) k) := by rw [hgslide]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.simple j) *
                    bubbleGroup (n + 1) k) := by rw [groupLift_simple]
              _ = groupLift n
                    ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ) *
                      (CoxeterMatrix.A n).toCoxeterSystem.simple j) *
                    bubbleGroup (n + 1) k := by rw [map_mul]; simp [mul_assoc]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd
                    (typeANormalForm n (τ * adjacentTransposition j))) *
                    bubbleGroup (n + 1) k := by rw [ih]
          · have hik : (i : ℕ) ≤ k := Nat.le_of_not_gt hbelow
            have hne : (k : ℕ) ≠ i := by
              intro h
              apply hcancel
              exact Fin.ext h
            have hne' : (k : ℕ) ≠ (i : ℕ) + 1 := by
              intro h
              apply hstep
              apply Fin.ext
              simpa using h
            have habove : (i : ℕ) + 1 < k := by omega
            have hi : i ≠ Fin.last n := by
              intro hi
              subst i
              have hk_le : (k : ℕ) ≤ n + 1 := Nat.le_of_lt_succ k.isLt
              simp only [Fin.val_last] at habove
              omega
            let a : Fin n := i.castPred hi
            have ha : a.castSucc = i := Fin.castSucc_castPred i hi
            have hnew : permDecomposition (n + 1) (σ * adjacentTransposition i) =
                  (k, τ * adjacentTransposition a) := by
              apply permDecomposition_eq_of_spec
              calc
                σ * adjacentTransposition i =
                    (permLift (n + 1) τ * bubblePerm (n + 1) k) *
                      adjacentTransposition i := by rw [hσ]
                _ = permLift (n + 1) τ *
                      (bubblePerm (n + 1) k * adjacentTransposition i) := by simp [mul_assoc]
                _ = permLift (n + 1) τ *
                      (adjacentTransposition i * bubblePerm (n + 1) k) := by
                        rw [bubblePerm_comm (n + 1) i k habove]
                _ = permLift (n + 1) τ *
                      (permLift (n + 1) (adjacentTransposition a) * bubblePerm (n + 1) k) := by
                        rw [permLift_adjacent, ha]
                _ = permLift (n + 1) (τ * adjacentTransposition a) *
                      bubblePerm (n + 1) k := by rw [map_mul]; simp [mul_assoc]
            rw [typeANormalForm_prod_succ, hnew]
            calc
              (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                    bubbleGroup (n + 1) k) *
                  (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i =
                groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  (bubbleGroup (n + 1) k *
                    (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i) := by simp [mul_assoc]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  ((CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple i *
                    bubbleGroup (n + 1) k) := by rw [bubbleGroup_comm_simple (n + 1) i k habove]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ)) *
                  (groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.simple a) *
                    bubbleGroup (n + 1) k) := by rw [groupLift_simple, ha]
              _ = groupLift n
                    ((CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n τ) *
                      (CoxeterMatrix.A n).toCoxeterSystem.simple a) *
                    bubbleGroup (n + 1) k := by rw [map_mul]; simp [mul_assoc]
              _ = groupLift n ((CoxeterMatrix.A n).toCoxeterSystem.wordProd
                    (typeANormalForm n (τ * adjacentTransposition a))) *
                    bubbleGroup (n + 1) k := by rw [ih]

/-- 挿入ソート標準形の像は単純生成元の右乗法で閉じる。

`i` と末尾要素の位置を比較する。離れていれば可換関係、境界を横切れば長さ三の braid 関係、
同じ互換が隣接すれば二次関係 `sᵢ²=1` で標準語を更新する。各場合で得た語は
`σ * adjacentTransposition i` の挿入ソート標準語に一致する。 -/
theorem typeANormalForm_mul_simple (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n σ) *
        (CoxeterMatrix.A n).simple i =
      (CoxeterMatrix.A n).toCoxeterSystem.wordProd
        (typeANormalForm n (σ * adjacentTransposition i)) := by
  exact typeANormalForm_mul_simple_aux n σ i

/-- 型 A の標準準同型は単射である。

任意の Coxeter 語について `typeANormalForm_spec` の恒等基底から始め、
`typeANormalForm_mul_simple` を各文字に適用して、その群元が像の置換の標準語に等しいことを示す。
従って `typeAHom x = typeAHom y` なら両者は同じ標準語の積に等しい。 -/
theorem typeAHom_injective (n : ℕ) : Function.Injective (typeAHom n) := by
  rcases typeANormalForm_spec n with ⟨hone, _⟩
  have hretract : ∀ w : (CoxeterMatrix.A n).Group,
      w = (CoxeterMatrix.A n).toCoxeterSystem.wordProd (typeANormalForm n (typeAHom n w)) := by
    intro w
    apply (CoxeterMatrix.A n).toCoxeterSystem.simple_induction_right w
    · rw [map_one, hone, CoxeterSystem.wordProd_nil]
    · intro w i hw
      rw [map_mul]
      change w * (CoxeterMatrix.A n).toCoxeterSystem.simple i =
        (CoxeterMatrix.A n).toCoxeterSystem.wordProd
          (typeANormalForm n (typeAHom n w * adjacentTransposition i))
      calc
        w * (CoxeterMatrix.A n).toCoxeterSystem.simple i =
            (CoxeterMatrix.A n).toCoxeterSystem.wordProd
                (typeANormalForm n (typeAHom n w)) *
              (CoxeterMatrix.A n).toCoxeterSystem.simple i := by rw [← hw]
        _ = _ := typeANormalForm_mul_simple n (typeAHom n w) i
  intro x y hxy
  calc
    x = (CoxeterMatrix.A n).toCoxeterSystem.wordProd
        (typeANormalForm n (typeAHom n x)) := hretract x
    _ = (CoxeterMatrix.A n).toCoxeterSystem.wordProd
        (typeANormalForm n (typeAHom n y)) := by rw [hxy]
    _ = y := (hretract y).symm

/-- 型 `Aₙ` Coxeter 群と `Fin (n+1)` 上の対称群の標準乗法同型。 -/
noncomputable def typeAEquivPerm (n : ℕ) :
    (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective (typeAHom n) ⟨typeAHom_injective n, typeAHom_surjective n⟩

/-- 型 A の標準乗法同型は単純反射を隣接互換へ送る。 -/
@[simp]
theorem typeAEquivPerm_simple (n : ℕ) (i : Fin n) :
    typeAEquivPerm n ((CoxeterMatrix.A n).simple i) = adjacentTransposition i := by
  exact typeAHom_simple n i

end SerrePositivity.Coxeter
