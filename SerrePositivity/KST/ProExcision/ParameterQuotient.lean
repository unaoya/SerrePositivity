module

public import SerrePositivity.KST.ProExcision.IteratedQuotient

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 生成イデアル倍と反復する通常商

概要：反復スカラー商の核を生成イデアル倍として表示する。
方針：部分加群の包含を各生成元のスカラー作用で判定する。
規約：任意の可換環と任意の加群。有限生成性は不要。
使われ方：KST Lemma 4.10 の Hⁱ(K)/a(n) という通常の表示。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- 概要：生成部分加群の包含は各パラメータの作用の包含と同値。
方針：列長についてスカラー像の和を分解する。
規約：任意の部分加群を標的とする。
使われ方：KST Lemma 4.10 の反復商の核と生成イデアル倍の同定。 -/
theorem parameterSubmodule_le_iff : ∀ {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R)
    (N : Submodule R M), parameterSubmodule z M ≤ N ↔ ∀ (j : Fin e) (x : M), z j • x ∈ N
  | 0, _, _, _ => by simp [parameterSubmodule]
  | e + 1, z, M, N => by
      rw [parameterSubmodule, sup_le_iff, parameterSubmodule_le_iff]
      constructor
      · rintro ⟨h, hlast⟩ j x
        refine Fin.lastCases ?_ (fun k ↦ ?_) j
        · exact hlast ⟨x, rfl⟩
        · exact h k x
      · intro h
        constructor
        · exact fun j x ↦ h j.castSucc x
        · rintro _ ⟨x, rfl⟩
          exact h (Fin.last e) x

/-- 概要：反復スカラー像の和は、生成イデアルによる加群倍。
方針：一方は生成元を含むこと、他方はイデアルの生成に関する帰納法を使う。
規約：外積表示や複体は使わない。
使われ方：KST Lemma 4.10 の通常のイデアル商との比較。 -/
theorem parameterSubmodule_eq_ideal_smul {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    parameterSubmodule z M = Ideal.span (Set.range z) • (⊤ : Submodule R M) := by
  apply le_antisymm
  · apply (parameterSubmodule_le_iff z M _).mpr
    intro j x
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_range_self j)) Submodule.mem_top
  · apply Submodule.smul_le.mpr
    intro r hr x _
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨j, rfl⟩ := hr
      exact (parameterSubmodule_le_iff z M _).mp le_rfl j x
    | zero => simp
    | add r s hr hs ihr ihs =>
      simpa only [add_smul] using Submodule.add_mem _ ihr ihs
    | smul r s hs ih =>
      simpa only [smul_eq_mul, mul_smul] using Submodule.smul_mem (parameterSubmodule z M) r ih

/-- 概要：反復冪商への標準射の核はパラメータ冪の生成イデアル倍。
方針：反復商の核の計算と生成部分加群の同定を合成する。
規約：任意の自然数冪。使われ方：KST Lemma 4.10 の通常商からの比較の降下。 -/
theorem iteratedPowerQuotientProjection_ker_ideal {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((iteratedPowerQuotientProjection z M).app n).hom.ker =
      Ideal.span (Set.range (fun j ↦ z j ^ n)) • (⊤ : Submodule R M) := by
  rw [iteratedPowerQuotientProjection_ker, parameterSubmodule_eq_ideal_smul]

/-- 概要：大きいパラメータ冪の生成部分加群は小さい冪のものに入る。
方針：各生成元の冪を分解し、生成部分加群の普遍性を使う。
規約：n≤m。使われ方：KST Lemma 4.10 の通常のイデアル商の遷移。 -/
theorem parameterSubmodule_powers_le {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R)
    {m n : ℕ} (h : n ≤ m) :
    parameterSubmodule (fun j ↦ z j ^ m) M ≤ parameterSubmodule (fun j ↦ z j ^ n) M := by
  apply (parameterSubmodule_le_iff _ M _).mpr
  intro j x
  have hx := (parameterSubmodule_le_iff (fun j ↦ z j ^ n) M _).mp le_rfl j
    (z j ^ (m - n) • x)
  simpa only [← mul_smul, ← pow_add, Nat.add_sub_of_le h] using hx

/-- 概要：パラメータ冪の生成イデアル倍の包含。
方針：生成部分加群の表示で冪の単調性を使う。
規約：n≤m。使われ方：KST Lemma 4.10 の通常商の遷移の定義。 -/
theorem parameterIdeal_powers_le {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R)
    {m n : ℕ} (h : n ≤ m) :
    Ideal.span (Set.range (fun j ↦ z j ^ m)) • (⊤ : Submodule R M) ≤
      Ideal.span (Set.range (fun j ↦ z j ^ n)) • (⊤ : Submodule R M) := by
  rw [← parameterSubmodule_eq_ideal_smul, ← parameterSubmodule_eq_ideal_smul]
  exact parameterSubmodule_powers_le z M h

/-- 概要：減少する部分加群による通常商の塔。
方針：恒等線形写像を商へ降ろし、代表元で合成律を確認する。
規約：部分加群の任意の減少列。使われ方：KST Lemma 4.10 の通常商の塔。 -/
def submoduleQuotientTower (M : ModuleCat.{u} R) (P : ℕ → Submodule R M)
    (hP : Antitone P) : Tower (ModuleCat.{u} R) where
  obj n := ModuleCat.of R (M ⧸ P n)
  transition h := ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (hP h))
  transition_self n := by
    apply ModuleCat.hom_ext
    change (P n).mapQ (P n) LinearMap.id (hP (le_refl n)) = LinearMap.id
    exact Submodule.mapQ_id (P n) (hP (le_refl n))
  transition_comp {k m n} hm hn := by
    apply ModuleCat.hom_ext
    change ((P m).mapQ (P n) LinearMap.id (hP hn)).comp
      ((P k).mapQ (P m) LinearMap.id (hP hm)) = (P k).mapQ (P n) LinearMap.id (hP (hn.trans hm))
    exact (Submodule.mapQ_comp (P k) (P m) (P n) LinearMap.id LinearMap.id
      (hP hm) (hP hn) (hP (hn.trans hm))).symm

/-- 概要：通常のパラメータ冪の生成イデアルによる商の塔。
方針：冪イデアルの包含を通常商の一般構成へ渡す。
規約：イデアルは (a₁ⁿ,…,aᵣⁿ)。使われ方：KST Lemma 4.10 の通常商側。 -/
def parameterQuotientTower {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    Tower (ModuleCat.{u} R) :=
  submoduleQuotientTower M
    (fun n ↦ Ideal.span (Set.range (fun j ↦ z j ^ n)) • (⊤ : Submodule R M))
    (fun _ _ h ↦ parameterIdeal_powers_le z M h)

/-- 概要：通常の生成イデアル商と反復するスカラー商の標準同型。
方針：標準全射の核の計算を第一同型定理へ適用する。
規約：任意の加群に成立。使われ方：KST Lemma 4.10 の比較の始域の同定。 -/
def parameterQuotientIso {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) (n : ℕ) :
    (parameterQuotientTower z M).obj n ≅ (iteratedPowerQuotientTower z M).obj n :=
  ((Submodule.quotEquivOfEq _ _ (iteratedPowerQuotientProjection_ker_ideal z M n).symm).trans
    (((iteratedPowerQuotientProjection z M).app n).hom.quotKerEquivOfSurjective
      (iteratedPowerQuotientProjection_surjective z M n))).toModuleIso

/-- 概要：標準同型は元の加群の代表元を標準全射の像へ送る。
方針：核による商の第一同型定理の計算則を使う。
規約：元の加群の元で評価。使われ方：KST Lemma 4.10 の比較射の自然性。 -/
theorem parameterQuotientIso_mk {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) (n : ℕ) (x : M) :
    (parameterQuotientIso z M n).hom.hom (Submodule.Quotient.mk x) =
      ((iteratedPowerQuotientProjection z M).app n).hom x := by
  change (((iteratedPowerQuotientProjection z M).app n).hom.quotKerEquivOfSurjective
    (iteratedPowerQuotientProjection_surjective z M n)) (Submodule.Quotient.mk x) = _
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    ((iteratedPowerQuotientProjection z M).app n).hom
    (iteratedPowerQuotientProjection_surjective z M n) x

/-- 概要：通常の生成イデアル商と反復商の同型は冪遷移に自然。
方針：商の代表元へ戻し、元の加群から反復商への射の自然性を使う。
規約：実際の両塔のレベル射。使われ方：KST Lemma 4.10 の通常商からの pro 比較。 -/
def parameterQuotientComparison {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    LevelHom (parameterQuotientTower z M) (iteratedPowerQuotientTower z M) where
  app n := (parameterQuotientIso z M n).hom
  naturality {m n} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (parameterQuotientIso z M n).hom.hom (Submodule.Quotient.mk x) = _
      rw [parameterQuotientIso_mk]
      have he := congrArg (fun f ↦ f.hom x) ((iteratedPowerQuotientProjection z M).naturality h)
      change ((iteratedPowerQuotientProjection z M).app n).hom x = _ at he
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he ⊢
      rw [parameterQuotientIso_mk]
      exact he

/-- 概要：通常の生成イデアル商と反復商の比較は pro 同型。
方針：各段の標準同型の逆射を使う。
規約：有限性・Noether 性は不要。使われ方：KST Lemma 4.10 の始域の標準化。 -/
theorem parameterQuotientComparison_isProIso {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    IsProIso (parameterQuotientComparison z M) := by
  intro n
  refine ⟨n, le_refl n, (parameterQuotientIso z M n).inv, ?_, ?_⟩
  · change (parameterQuotientIso z M n).hom ≫ (parameterQuotientIso z M n).inv = _
    rw [Iso.hom_inv_id, Tower.transition_self]
  · change (parameterQuotientIso z M n).inv ≫ (parameterQuotientIso z M n).hom = _
    rw [Iso.inv_hom_id, Tower.transition_self]

end SerrePositivity.KST.ProExcision
