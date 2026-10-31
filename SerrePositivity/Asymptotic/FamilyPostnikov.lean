module

public import SerrePositivity.Asymptotic.FamilyHomologyTruncation
public import SerrePositivity.CategoryTheory.Derived

/-!
# 導来対象の族に対する共通の有限 Postnikov 帰納法

族の性質 P が成分ごとの同型と完全三角形による拡大で閉じるとき、
ホモロジー列を一つの次数に置いた族から、共通有界な族全体へ P を拡張する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]
  (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  (P : (ℕ → DerivedCategory (ModuleCat.{u} R)) → Prop)
  (hiso : ∀ {X Y}, P X → (∀ n, X n ≅ Y n) → P Y)
  (hext : ∀ (T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} R))),
    (∀ n, T n ∈ distTriang _) → P (fun n ↦ (T n).obj₁) →
      P (fun n ↦ (T n).obj₃) → P (fun n ↦ (T n).obj₂))
  (hpure : ∀ (M : ModuleSequence R), Q M → ∀ q : ℤ,
    P (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat R) q).obj (M.obj ⟨n⟩)))

include hiso hpure in
omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- 単一次数の場合のホモロジーによる帰着。 -/
lemma familyPostnikov_pure (X : ℕ → DerivedCategory (ModuleCat.{u} R)) (q : ℤ)
    (hge : ∀ n, (X n).IsGE q) (hle : ∀ n, (X n).IsLE q)
    (hH : Q (Discrete.functor
      (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj (X n)))) : P X :=
  hiso (hpure _ hH q) (fun n ↦ (derivedPureHomologyIso (X n) q).symm)

include hiso hext hpure in
/-- 共通の有限次数幅に関する Postnikov 帰納法。 -/
lemma familyPostnikov_finiteAmplitude (w : ℕ)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hge : ∀ n, (K n).IsStrictlyGE a) (hle : ∀ n, (K n).IsStrictlyLE (a + w))
    (hH : ∀ q, Q (familyHomology K q)) : P (fun n ↦ DerivedCategory.Q.obj (K n)) := by
  induction w generalizing K a with
  | zero =>
    have hle' (n : ℕ) : (K n).IsStrictlyLE a := by simpa using hle n
    exact familyPostnikov_pure Q P hiso hpure _ a (fun n ↦ inferInstance) (fun n ↦ inferInstance)
      (Q.prop_of_iso (familyDerivedHomologyIso K a).symm (hH a))
  | succ w ih =>
    let b : ℤ := a + w
    have hle' (n : ℕ) : (K n).IsStrictlyLE (b + 1) := by
      convert hle n using 1
      dsimp [b]
      omega
    have h₁ : P (fun n ↦ DerivedCategory.Q.obj ((K n).truncLE b)) :=
      ih (fun n ↦ (K n).truncLE b) a (fun n ↦ inferInstance) (fun n ↦ inferInstance)
        (familyHomology_truncLE_prop K Q hH b)
    have h₃ : P (fun n ↦ DerivedCategory.Q.obj ((K n).truncGE (b + 1))) :=
      familyPostnikov_pure Q P hiso hpure _ (b + 1) (fun n ↦ inferInstance) (fun n ↦ inferInstance)
        (Q.prop_of_iso
          (familyDerivedHomologyIso (fun n ↦ (K n).truncGE (b + 1)) (b + 1)).symm
          (familyHomology_truncGE_prop K Q hH (b + 1) (b + 1)))
    exact hext (fun n ↦ DerivedCategory.triangleOfSES ((K n).shortComplexTruncLE_shortExact b))
      (fun n ↦ DerivedCategory.triangleOfSES_distinguished _) h₁
      (hiso h₃ (fun n ↦
        (asIso (DerivedCategory.Q.map ((K n).shortComplexTruncLEX₃ToTruncGE b (b + 1) rfl))).symm))

include hiso hext hpure in
/-- 共通有界な導来対象の族への Postnikov 帰納法。 -/
theorem familyPostnikov_uniform (X : ℕ → DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hge : ∀ n, (X n).IsGE a) (hle : ∀ n, (X n).IsLE b)
    (hH : ∀ q, Q (Discrete.functor
      (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj (X n)))) : P X := by
  choose K hKa hKb he using
    (fun n ↦ DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE (X n) a b)
  have hKb' (n : ℕ) : (K n).IsStrictlyLE (a + (b - a).toNat) :=
    (K n).isStrictlyLE_of_le b _ (by omega)
  have hKH (q : ℤ) : Q (familyHomology K q) := Q.prop_of_iso
    (Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctor _ q).mapIso (he n.as).some) ≪≫
      familyDerivedHomologyIso K q) (hH q)
  exact hiso (familyPostnikov_finiteAmplitude Q P hiso hext hpure
    (b - a).toNat K a hKa hKb' hKH) (fun n ↦ (he n).some.symm)

end SerrePositivity.Asymptotic
