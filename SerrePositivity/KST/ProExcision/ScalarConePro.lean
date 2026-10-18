module

public import SerrePositivity.KST.ProExcision.ScalarConeHomology
public import SerrePositivity.KST.ProExcision.ConeNaturality

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 一変数 Koszul 比較の pro 同型

概要：有限生成ホモロジーの冪商を、冪スカラー cone のホモロジーへ比較する。
方針：長完全列の自然性と冪核の pro-消滅を使う。
規約：係数複体の項の有限性は仮定しない。
使われ方：KST Lemma 4.10 の一変数段階。原典のスペクトル系列を使わない。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：冪スカラーの可換正方形。
方針：aᵐ=aᵐ⁻ⁿaⁿ を用いる。
規約：右側は恒等射。使われ方：KST Lemma 4.10 の cone 冪遷移。 -/
theorem powerScalarSquare (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {m n : ℕ} (h : n ≤ m) :
    smulId (a ^ m) K ≫ 𝟙 K = smulId (a ^ (m - n)) K ≫ smulId (a ^ n) K := by
  simp only [smulId, Category.comp_id, Linear.comp_smul,
    smul_smul, ← pow_add, Nat.add_sub_of_le h]

/-- 概要：aᵐ の cone から aⁿ の cone への標準写像。
方針：左側は aᵐ⁻ⁿ 倍、右側は恒等射とする。
規約：n≤m。使われ方：KST Lemma 4.9・4.10 の一変数遷移。 -/
def powerScalarConeMap (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {m n : ℕ} (h : n ≤ m) :
    ((scalarConeFunctor (a ^ m)).obj K) ⟶ ((scalarConeFunctor (a ^ n)).obj K) :=
  CochainComplex.mappingCone.map _ _ (smulId (a ^ (m - n)) K) (𝟙 K)
    (powerScalarSquare a K h)

/-- 概要：冪スカラー cone の塔。
方針：可換正方形の合成則と指数の加法則を使う。
規約：添字零も含む。使われ方：KST Lemma 4.10 の一変数比較の標的。 -/
def powerScalarConeTower (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Tower (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj n := (scalarConeFunctor (a ^ n)).obj K
  transition h := powerScalarConeMap a K h
  transition_self n := by
    change CochainComplex.mappingCone.map _ _ _ _ _ =
      𝟙 (CochainComplex.mappingCone (smulId (a ^ n) K))
    simpa only [Nat.sub_self, pow_zero, smulId, one_smul] using
      CochainComplex.mappingCone.map_id (smulId (a ^ n) K)
  transition_comp {k m n} hm hn := by
    dsimp [powerScalarConeMap]
    rw [← CochainComplex.mappingCone.map_comp]
    congr 1
    · simp only [smulId, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        smul_smul, ← pow_add, show m - n + (k - m) = k - n by omega]

/-- 概要：冪が大きいスカラーの像は小さい冪の像に入る。
方針：大きい冪を小さい冪の倍にする。
規約：任意の係数加群。使われ方：KST Lemma 4.10 の通常商の遷移。 -/
theorem powerScalarRange_le (a : R) (M : ModuleCat.{u} R) {m n : ℕ} (h : n ≤ m) :
    (a ^ m • (LinearMap.id : M →ₗ[R] M)).range ≤
      (a ^ n • (LinearMap.id : M →ₗ[R] M)).range := by
  rintro _ ⟨x, rfl⟩
  refine ⟨a ^ (m - n) • x, ?_⟩
  change a ^ n • (a ^ (m - n) • x) = a ^ m • x
  rw [← mul_smul, ← pow_add, Nat.add_sub_of_le h]

/-- 概要：ホモロジーの冪スカラー商の塔。
方針：元のホモロジーの恒等射を各商へ降ろす。
規約：係数ホモロジーは固定。使われ方：KST Lemma 4.10 の一変数比較の始域。 -/
def powerHomologyQuotientTower (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Tower (ModuleCat.{u} R) where
  obj n := scalarHomologyQuotient (a ^ n) K i
  transition {m n} h := ModuleCat.ofHom
    (Submodule.mapQ _ _ LinearMap.id (powerScalarRange_le a (K.homology i) h))
  transition_self n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  transition_comp hm hn := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- 概要：cone への包含は冪遷移と可換する。
方針：cone の三角形の射の第二の可換性をホモロジーへ写す。
規約：右側は恒等写像。使われ方：KST Lemma 4.10 の比較射の自然性。 -/
theorem powerScalarConeMap_inr (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {m n : ℕ} (h : n ≤ m) (i : ℤ) :
    homologyMap (CochainComplex.mappingCone.inr (smulId (a ^ m) K)) i ≫
        homologyMap (powerScalarConeMap a K h) i =
      homologyMap (CochainComplex.mappingCone.inr (smulId (a ^ n) K)) i := by
  have he := congrArg (homologyFunctor _ _ i).map
    (CochainComplex.mappingCone.triangleMap (smulId (a ^ m) K) (smulId (a ^ n) K)
      (smulId (a ^ (m - n)) K) (𝟙 K) (powerScalarSquare a K h)).comm₂
  change (homologyFunctor _ _ i).map
      (CochainComplex.mappingCone.inr (smulId (a ^ m) K) ≫ powerScalarConeMap a K h) =
    (homologyFunctor _ _ i).map
      (𝟙 K ≫ CochainComplex.mappingCone.inr (smulId (a ^ n) K)) at he
  simp only [Functor.map_comp, Category.id_comp] at he
  exact he

/-- 概要：通常の冪商から冪 cone ホモロジーへのレベル比較射。
方針：商の代表元で冪遷移との自然性を確認する。
規約：実際の cone のホモロジーを使用。使われ方：KST Lemma 4.10 の一変数比較。 -/
def powerScalarConeComparison (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    LevelHom (powerHomologyQuotientTower a K i)
      ((powerScalarConeTower a K).map (homologyFunctor _ _ i)) where
  app n := scalarConeHomologyComparison (a ^ n) K i
  naturality {m n} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      exact (congrArg (fun f ↦ f.hom x) (powerScalarConeMap_inr a K h i)).symm

/-- 概要：冪 cone の連結写像を次次数の冪核へ制限する。
方針：長完全列の零合成と連結写像の自然性を使う。
規約：冪核の遷移は冪倍。使われ方：KST Lemma 4.10 の余核の pro-零化。 -/
def powerScalarConeConnecting (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    LevelHom ((powerScalarConeTower a K).map (homologyFunctor _ _ i))
      (powerKernelTower a (K.homology (i + 1))) where
  app n := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨(Cone.δ (smulId (a ^ n) K) i (i + 1) rfl).hom x,
        scalarCone_connecting_smul_zero (a ^ n) K i x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add _ x y)
      map_smul' := fun r x ↦ Subtype.ext (map_smul _ r x) }
  naturality {m n} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have he := cone_connecting_naturality (smulId (a ^ m) K) (smulId (a ^ n) K)
      (smulId (a ^ (m - n)) K) (𝟙 K) (powerScalarSquare a K h) i (i + 1) rfl
    have hh := congrArg (fun f ↦ f.hom x) he
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, smulId,
      homologyMap_smul, homologyMap_id, ModuleCat.hom_smul,
      ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] at hh
    exact hh

/-- 概要：一変数 Koszul 比較は次次数のホモロジーが Noether なら pro 同型。
方針：比較の単射性、連結写像での完全性、冪核の pro-零性を組み合わせる。
規約：原典のスペクトル系列証明を cone 長完全列へ置き換えた。
使われ方：KST Lemma 4.10 の列長帰納法の一変数段階。 -/
theorem powerScalarConeComparison_isProIso
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [IsNoetherian R (K.homology (i + 1))] : IsProIso (powerScalarConeComparison a K i) := by
  apply proIso_of_injective_exact_proZero (powerScalarConeComparison a K i)
    (powerScalarConeConnecting a K i)
  · intro n
    exact scalarConeHomologyComparison_injective (a ^ n) K i
  · intro n x
    change (⟨(Cone.δ (smulId (a ^ n) K) i (i + 1) rfl).hom x, _⟩ :
      powerKernel a (K.homology (i + 1)) n) = 0 ↔ _
    rw [Subtype.ext_iff]
    exact scalarConeHomologyComparison_exact (a ^ n) K i x
  · exact powerKernelTower_isProZero a (K.homology (i + 1))

end SerrePositivity.KST.ProExcision
