module

public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Length
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# `Tor` を `R` 加群として見る

Mathlib の `CategoryTheory.Tor (ModuleCat R) i` は `X ⊗ -` の左導来関手（第 2 変数で導来）である。
ここではその対象を `R` 加群の型として取り出し、`Module.length` をとる。

規約（`notes/PLAN.md` §1.3）：`Tor ≅ Tor'`（対称性）は Mathlib に未証明なので、
このプロジェクトでは Tor の対称性を使わない。

後半では、係数環上の加群としての `TorAlg`、コチェイン分解によるその計算、
もとの加群を消す元が Tor も消すことを扱う。
-/

@[expose] public section

open CategoryTheory

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- `Tor_i^R(M, N)` を `R` 加群の型として見たもの。
`CategoryTheory.Tor (ModuleCat R) i` の対象の台集合で、第 2 変数 `N` の射影分解で計算される。 -/
noncomputable abbrev TorModule (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Type u :=
  ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- `length_R Tor_i^R(M, N)`（`ℕ∞` 値）。 -/
noncomputable def torLength (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℕ∞ :=
  Module.length R (TorModule R i M N)

end SerrePositivity

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- `R` 代数 `C`（構造は環準同型 `φ : R →+* C` で与える）と `R` 加群 `N` に対する
`Tor_i^R(C, N)` を、係数拡大関手 `N ↦ C ⊗_R N : ModuleCat R ⥤ ModuleCat C` の
左導来関手として定め、`C` 加群の型として見たもの。
`φ` を取り替えることで、§5.1 の `ι_σ` によるひねりを表せる。 -/
noncomputable abbrev TorAlg {C : Type u} [CommRing C] (φ : R →+* C) (i : ℕ)
    (N : Type u) [AddCommGroup N] [Module R N] : Type u :=
  ((ModuleCat.extendScalars φ).leftDerived i).obj (ModuleCat.of R N)

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

open Limits

/-- 線形同値な加群の `Tor` は線形同値。 -/
noncomputable def torAlgCongr (i : ℕ) {V W : Type u} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] (e : V ≃ₗ[A] W) : TorAlg φ i V ≃ₗ[C] TorAlg φ i W :=
  (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).mapIso e.toModuleIso).toLinearEquiv

/-- 零加群の `Tor` は零。 -/
lemma torAlg_subsingleton (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V] [Subsingleton V] :
    Subsingleton (TorAlg φ i V) := by
  have hz : IsZero (ModuleCat.of A V) := ModuleCat.isZero_of_subsingleton _
  have : Projective (ModuleCat.of A V) := hz.projective
  rcases i with _ | i
  · -- `Tor_0 ≅ F.obj V`：`F = extendScalars φ` は左随伴なので有限余極限を保つ
    have : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ) := by
      have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).leftAdjoint_preservesColimits
      infer_instance
    exact ModuleCat.subsingleton_of_isZero
      ((((ModuleCat.extendScalars.{u, u, u} φ).leftDerivedZeroIsoSelf).app
        (ModuleCat.of A V)).isZero_iff.mpr
        ((ModuleCat.extendScalars.{u, u, u} φ).map_isZero hz))
  · exact ModuleCat.subsingleton_of_isZero
      ((ModuleCat.extendScalars.{u, u, u} φ).isZero_leftDerived_obj_projective_succ i _)

end SerrePositivity

end

/-!
## `Tor` を ℤ 添字 cochain 複体の分解で計算する

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

end

/-!
## `Tor` と消去イデアル

`a ∈ A` が `V` 上で零なら、`φ a` は `Tor_i^A(C, V)`（`TorAlg φ i V`）上で零。

証明：`a • 𝟙 V = 0` なので `(F.leftDerived i).map (a • 𝟙 V) = (F.leftDerived i).map 0 = 0`。
一方、射影分解 `P` の上では `a • 𝟙 P` が `a • 𝟙 V` を持ち上げるので、
`Functor.leftDerived_map_eq` により `(F.leftDerived i).map (a • 𝟙 V)` は
`H_i(F(a • 𝟙 P)) = H_i(φ a • 𝟙) = φ a • 𝟙` と同型で移り合う。
よって `φ a • 𝟙 = 0`。

途中で使う補題：`single`、`homologyMap` がスカラー倍と両立すること（`Basic.lean`）と、
係数拡大 `F.mapHomologicalComplex` がスカラー倍を `φ` 倍に送ること（`BaseChange.lean`）。
`notes/PLAN.md` §11 の B3。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- `a` が `V` を消すなら `φ a` は `Tor_i^A(C, V)` を消す。 -/
theorem torAlg_smul_eq_zero (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V] (a : A)
    (ha : ∀ v : V, a • v = 0) (x : TorAlg φ i V) : φ a • x = 0 := by
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let X := ModuleCat.of A V
  let P := projectiveResolution X
  have hf : (a • 𝟙 X : X ⟶ X) = 0 := ModuleCat.hom_ext (LinearMap.ext ha)
  have hw : (a • 𝟙 P.complex) ≫ P.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} A)).map (a • 𝟙 X) := by
    rw [single_map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  have h1 := F.leftDerived_map_eq i (a • 𝟙 X) (P := P) (Q := P) (a • 𝟙 P.complex) hw
  have h2 : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ i).map
      (a • 𝟙 P.complex) = φ a • 𝟙 _ := by
    rw [Functor.comp_map, extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
      HomologicalComplex.homologyFunctor_map, homologyMap_smul, HomologicalComplex.homologyMap_id]
    rfl
  have h3 : (F.leftDerived i).map (a • 𝟙 X) = φ a • 𝟙 _ := by
    rw [h1, h2, Linear.smul_comp, Linear.comp_smul]
    erw [Category.id_comp]
    rw [Iso.hom_inv_id]
  have h4 : (F.leftDerived i).map (a • 𝟙 X) = 0 := by
    rw [hf, F.leftDerived_map_eq i (0 : X ⟶ X) (P := P) (Q := P) 0 (by simp), Functor.map_zero]
    erw [Limits.zero_comp]
    rw [Limits.comp_zero]
  have h5 : (φ a • 𝟙 ((F.leftDerived i).obj X) : _ ⟶ _) = 0 := h3.symm.trans h4
  have := congrArg (fun g : (F.leftDerived i).obj X ⟶ (F.leftDerived i).obj X ↦ g.hom x) h5
  simpa using this

end SerrePositivity

end
