module

public import SerrePositivity.Perfect
public import SerrePositivity.ResolutionOfCochain
public import SerrePositivity.Tor

/-!
# `Tor` を ℤ 添字 cochain 複体の分解で計算する

`K` が `Z` の分解（`IsResolutionOf K (ModuleCat.of A Z)`）なら、`A` 代数 `C`（`φ : A →+* C`）に
対して `Tor_i^A(Z, C) ≅ H^{-i}(C ⊗_A K)`。左導来関手を射影分解 `toChain K` で計算し
（`ProjectiveResolution.isoLeftDerivedObj`）、係数拡大が制限と両立すること、
`toChain` のホモロジーが元の複体のホモロジーであることをつなぐ。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 基底変更した複体も正の次数で零。 -/
lemma baseChange_isZero_X_of_pos (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) (i : ℤ) (hi : 0 < i) :
    IsZero ((baseChange φ K).X i) :=
  (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hK i hi)

/-- **`Tor` と cochain 分解**：`Tor_i^A(Z, C) ≅ H^{-i}(C ⊗_A K)`。 -/
noncomputable def torIsoCochain {Z : Type u} [AddCommGroup Z] [Module A Z]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsResolutionOf K (ModuleCat.of A Z)) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A Z) ≅
      (baseChange φ K).homology (-(i : ℤ)) :=
  h.toProjectiveResolution.isoLeftDerivedObj (ModuleCat.extendScalars.{u, u, u} φ) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso
      (mapRestrictionIso (ModuleCat.extendScalars.{u, u, u} φ) K) ≪≫
    toChainHomologyIso _ (baseChange_isZero_X_of_pos φ _ h.isZero_X) i

end SerrePositivity
