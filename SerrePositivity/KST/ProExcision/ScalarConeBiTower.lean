module

public import SerrePositivity.KST.ProExcision.BiTower
public import SerrePositivity.KST.ProExcision.ScalarQuotient
public import SerrePositivity.KST.ProExcision.ScalarConePro

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 動く係数複体上の冪 cone の二重塔

概要：係数複体の塔と、独立な末尾変数の冪指数を組み合わせる。
方針：可換正方形の cone を長方形の遷移へ適用する。
規約：係数複体の添字と末尾変数の指数は別々に動く。
使われ方：KST Lemma 4.9・4.10 の列長帰納法。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：動く係数と冪指数のスカラー正方形。
方針：線形性と指数の加法則を使う。
規約：左辺の冪が大きい。使われ方：KST Lemma 4.10 の二重塔の遷移。 -/
theorem powerScalarSquare_map (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    {m n : ℕ} (h : n ≤ m) :
    smulId (a ^ m) K ≫ f = (a ^ (m - n) • f) ≫ smulId (a ^ n) L := by
  simp only [smulId, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
    Category.comp_id, smul_smul, ← pow_add, Nat.add_sub_of_le h]

/-- 概要：動く係数上の末尾変数の冪 cone の二重塔。
方針：右成分は係数遷移、左成分は冪倍した係数遷移とする。
規約：第一添字が係数、第二添字が末尾変数の冪。
使われ方：KST Lemma 4.9・4.10 の独立指数の帰納段階。 -/
def powerScalarConeBiTower (a : R) (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) :
    BiTower (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj n k := (scalarConeFunctor (a ^ k)).obj (X.obj n)
  transition {m n k l} h h' :=
    CochainComplex.mappingCone.map _ _ (a ^ (k - l) • X.transition h) (X.transition h)
      (powerScalarSquare_map a (X.transition h) h')
  transition_self n k := by
    rw [X.transition_self]
    change CochainComplex.mappingCone.map _ _ _ _ _ =
      𝟙 (CochainComplex.mappingCone (smulId (a ^ k) (X.obj n)))
    simpa only [Nat.sub_self, pow_zero, one_smul] using
      CochainComplex.mappingCone.map_id (smulId (a ^ k) (X.obj n))
  transition_comp {m n p k l q} h₁ h₂ h₃ h₄ := by
    rw [← CochainComplex.mappingCone.map_comp]
    congr 1
    · simp only [Linear.smul_comp, Linear.comp_smul, X.transition_comp,
        smul_smul, ← pow_add, show l - q + (k - l) = k - q by omega]
    · exact X.transition_comp h₁ h₂

/-- 概要：二重冪 cone の行の遷移は通常の一変数冪 cone 遷移に一致する。
方針：固定された係数添字の自己遷移を恒等射にする。
規約：対象複体は X の固定段。使われ方：KST Lemma 4.10 の一変数比較の再利用。 -/
theorem powerScalarConeBiTower_row_transition (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℕ)
    {m k : ℕ} (h : k ≤ m) :
    ((powerScalarConeBiTower a X).row n).transition h = powerScalarConeMap a (X.obj n) h := by
  dsimp [BiTower.row, powerScalarConeBiTower, powerScalarConeMap]
  simp only [X.transition_self]
  rfl

/-- 概要：線形写像は大きい冪の像を小さい冪の像へ送る。
方針：線形性でスカラーを外へ出し、冪指数を分解する。
規約：任意の係数加群。使われ方：KST Lemma 4.10 の二重塔の通常商。 -/
theorem powerScalarRange_map (a : R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    {m n : ℕ} (h : n ≤ m) :
    (a ^ m • (LinearMap.id : M →ₗ[R] M)).range ≤
      Submodule.comap f.hom (a ^ n • (LinearMap.id : N →ₗ[R] N)).range := by
  rintro _ ⟨x, rfl⟩
  refine ⟨a ^ (m - n) • f.hom x, ?_⟩
  change a ^ n • (a ^ (m - n) • f.hom x) = f.hom (a ^ m • x)
  rw [map_smul, ← mul_smul, ← pow_add, Nat.add_sub_of_le h]

/-- 概要：動くホモロジーの通常冪商の二重塔。
方針：係数のホモロジー写像を、冪倍の像による商へ降ろす。
規約：第一添字は係数、第二添字は冪指数。
使われ方：KST Lemma 4.10 の反復 cone への比較の始域。 -/
def powerHomologyQuotientBiTower (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) : BiTower (ModuleCat.{u} R) where
  obj n k := scalarHomologyQuotient (a ^ k) (X.obj n) i
  transition {m n k l} h h' := ModuleCat.ofHom (Submodule.mapQ _ _
    (homologyMap (X.transition h) i).hom (powerScalarRange_map a _ h'))
  transition_self n k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      dsimp only [Submodule.mapQ, ModuleCat.ofHom, Submodule.liftQ_apply]
      rw [X.transition_self, homologyMap_id]
      rfl
  transition_comp h₁ h₂ h₃ h₄ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk
        ((homologyMap (X.transition h₂) i).hom ((homologyMap (X.transition h₁) i).hom x)) =
        Submodule.Quotient.mk ((homologyMap (X.transition (h₂.trans h₁)) i).hom x)
      congr 1
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← homologyMap_comp,
        X.transition_comp]

/-- 概要：二重冪商の行の遷移は固定係数の通常冪商の遷移。
方針：係数の自己遷移とそのホモロジー写像を恒等写像へ簡約する。
規約：冪指数だけが動く。使われ方：KST Lemma 4.10 の一変数比較の再利用。 -/
theorem powerHomologyQuotientBiTower_row_transition (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℕ) (i : ℤ)
    {m k : ℕ} (h : k ≤ m) :
    ((powerHomologyQuotientBiTower a X i).row n).transition h =
      (powerHomologyQuotientTower a (X.obj n) i).transition h := by
  dsimp [BiTower.row, powerHomologyQuotientBiTower]
  simp only [X.transition_self, homologyMap_id]
  rfl

/-- 概要：通常の冪商から冪 cone ホモロジーへの二重塔の比較。
方針：可換正方形の cone 包含との可換性を商の代表元で使う。
規約：両方の添字に自然。使われ方：KST Lemma 4.10 の対角比較。 -/
def powerScalarConeBiComparison (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    BiLevelHom (powerHomologyQuotientBiTower a X i)
      ((powerScalarConeBiTower a X).map (homologyFunctor _ _ i)) where
  app n k := scalarConeHomologyComparison (a ^ k) (X.obj n) i
  naturality {m n k l} h h' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have he := congrArg (homologyFunctor _ _ i).map
        (CochainComplex.mappingCone.triangleMap (smulId (a ^ k) (X.obj m))
          (smulId (a ^ l) (X.obj n)) (a ^ (k - l) • X.transition h)
          (X.transition h) (powerScalarSquare_map a (X.transition h) h')).comm₂
      simp only [Functor.map_comp] at he
      exact (congrArg (fun f ↦ f.hom x) he).symm

/-- 概要：各係数段で有限な冪核を持つ二重 cone 比較は、対角でも pro 同型。
方針：固定係数の一変数比較を各行へ適用し、対角の一般補題を使う。
規約：係数段について torsion 指数の一様性は要求しない。
使われ方：KST Lemma 4.10 の列を一つ延ばす段階。 -/
theorem powerScalarConeBiComparison_diagonal_isProIso (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ)
    (hX : ∀ n, IsNoetherian R ((X.obj n).homology (i + 1))) :
    IsProIso (powerScalarConeBiComparison a X i).diagonal := by
  apply BiLevelHom.diagonal_isProIso
  intro n k
  letI := hX n
  obtain ⟨m, h, g, hg, gh⟩ := powerScalarConeComparison_isProIso a (X.obj n) i k
  refine ⟨m, h, g, ?_, ?_⟩
  · change scalarConeHomologyComparison (a ^ m) (X.obj n) i ≫ g =
      ((powerHomologyQuotientBiTower a X i).row n).transition h
    rw [powerHomologyQuotientBiTower_row_transition]
    exact hg
  · change g ≫ scalarConeHomologyComparison (a ^ k) (X.obj n) i =
      (homologyFunctor _ _ i).map (((powerScalarConeBiTower a X).row n).transition h)
    rw [powerScalarConeBiTower_row_transition]
    exact gh

end SerrePositivity.KST.ProExcision
