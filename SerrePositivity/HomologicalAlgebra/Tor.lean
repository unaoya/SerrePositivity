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
# `Tor` を加群として見る

## 概要

Mathlib の `Tor` は左導来関手として圏論的に定義されていて、その値は `ModuleCat R` の対象である。
このファイルでは、その対象の台集合を加群の型として取り出し、長さがとれるようにする。
二種類の `Tor` を使う。

- `TorModule R i M N`：Mathlib の `CategoryTheory.Tor (ModuleCat R) i`、すなわち `M ⊗_R -` の
  左導来関手を `N` に施したもの。Serre の交点重複度 `χ^R(M, N) = Σ (-1)^i ℓ(Tor_i^R(M, N))`
  （`IntersectionMultiplicity/Basic.lean`）の定義に使う。`torLength R i M N` はその長さ（`ℕ∞` 値）。
- `TorAlg φ i N`：環準同型 `φ : R →+* C` で `C` を `R` 代数とみなし、係数拡大関手
  `N ↦ C ⊗_R N : ModuleCat R ⥤ ModuleCat C` の左導来関手を `N` に施したもの。値は `C` 加群で、
  `Tor_i^R(C, N)` に `C` 加群の構造を入れたものに当たる。`C` 上の正規化長さ `λ` で `Tor` を測るとき
  （論文 (5.2) の `c_σ`、Lemma 3.4、Corollary 2.6）に使う。`φ` を取り替えることで、§5.1 のひねり
  `ι_σ` を同じ式で表せる。

## 規約（`notes/PLAN.md` §1.3）

Mathlib の `Tor` は第 2 変数で導来する。両変数の対称性 `Tor ≅ Tor'` は Mathlib に未証明なので、
このプロジェクトでは Tor の対称性を一切使わず、常に第 2 変数（`TorAlg` では `N`）を分解して
計算する。論文で `Tor_i^A(V, C)` と書かれるものは、ここでは `TorAlg φ i V`（`V` を分解）である。

## 内容

後半では `TorAlg` について次を示す。線形同値な加群の `Tor` は線形同値（`torAlgCongr`）、
零加群の `Tor` は零（`torAlg_subsingleton`）、`Tor` は ℤ 添字 cochain 複体の分解で計算できる
（`torIsoCochain`）、`N` を消す元 `a` の像 `φ(a)` は `Tor_i^R(C, N)` を消す（`torAlg_smul_eq_zero`）。
-/

@[expose] public section

open CategoryTheory

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- `Tor_i^R(M, N)` を `R` 加群の型として見たもの。Mathlib の `CategoryTheory.Tor (ModuleCat R) i`
（`M ⊗_R -` の左導来関手）を `N` に施した対象の台集合で、第 2 変数 `N` の射影分解 `P` に対して
`H_i(M ⊗_R P)` で計算される。交点重複度 `χ^R(M, N)` の定義に使う。 -/
noncomputable abbrev TorModule (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Type u :=
  ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- `Tor_i^R(M, N)` の `R` 加群としての長さ（`ℕ∞` 値。有限長でなければ `⊤`）。交点重複度
`χ^R(M, N) = Σ_i (-1)^i torLength R i M N` の各項になる。 -/
noncomputable def torLength (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℕ∞ :=
  Module.length R (TorModule R i M N)

end SerrePositivity

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 環準同型 `φ : R →+* C` で `C` を `R` 代数とみなし、係数拡大関手 `N ↦ C ⊗_R N`
（`ModuleCat R ⥤ ModuleCat C`）の左導来関手を `R` 加群 `N` に施した `C` 加群。`Tor_i^R(C, N)` に
`C` 加群の構造を入れたものに当たり、`N` の射影分解 `P` に対して `H_i(C ⊗_R P)` で計算される。
`C` 加群なので、`C` 上の正規化長さ `λ` で測ることができる。`φ` を §5.1 のひねり `ι_σ` に
取り替えることで、ひねった `Tor` を同じ式で表せる。 -/
noncomputable abbrev TorAlg {C : Type u} [CommRing C] (φ : R →+* C) (i : ℕ)
    (N : Type u) [AddCommGroup N] [Module R N] : Type u :=
  ((ModuleCat.extendScalars φ).leftDerived i).obj (ModuleCat.of R N)

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

open Limits

/-- `R` 加群の線形同値 `e : V ≃ₗ W` は、`Tor` の `C` 線形同値 `TorAlg φ i V ≃ₗ[C] TorAlg φ i W` を
誘導する。左導来関手が同型を同型に送ることによる。Lemma 3.4 の組成列の帰納法で、商加群 `V ⧸ N` を
剰余体と同一視して `Tor` を比べるときに使う。 -/
noncomputable def torAlgCongr (i : ℕ) {V W : Type u} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] (e : V ≃ₗ[A] W) : TorAlg φ i V ≃ₗ[C] TorAlg φ i W :=
  (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).mapIso e.toModuleIso).toLinearEquiv

/-- 零加群 `V` の `Tor_i^R(C, V)` は零である。`i = 0` では `Tor_0 ≅ C ⊗_R V`（左導来関手の `0` 次は
もとの関手。`extendScalars` は左随伴なので有限余極限を保ち、Mathlib の `leftDerivedZeroIsoSelf` が
使える）で、零加群のテンソル積は零。`i ≥ 1` では、零加群は射影的で、射影加群の高次の `Tor` は零
（`isZero_leftDerived_obj_projective_succ`）。 -/
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

`K` が `Z` の分解（`IsResolutionOf K (ModuleCat.of A Z)`、`Resolution.lean`）なら、`A` 代数 `C`
（`φ : A →+* C`）に対して `Tor_i^A(C, Z) ≅ H^{-i}(K ⊗_A C)` である（`torIsoCochain`）。
左導来関手は任意の射影分解で計算できる（Mathlib の `ProjectiveResolution.isoLeftDerivedObj`）ので、
`toChain K` を射影分解として使い、係数拡大が制限と可換であること（`mapRestrictionIso`）と、制限の
ホモロジーがもとの複体のホモロジーであること（`toChainHomologyIso`）をつなぐ。Koszul 複体で `Tor` を
計算すること（`CommutativeAlgebra/KoszulResolution.lean` の `torAlgKoszulEquiv`）と、Tor の長完全列
（`TorLES.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- **`Tor` を cochain 分解で計算する**：`K` が `Z` の分解なら `Tor_i^A(C, Z) ≅ H^{-i}(K ⊗_A C)`。
三つの同型の合成である。左導来関手の値は射影分解 `toChain K` 上で `H_i(C ⊗ toChain K)` と同型
（`isoLeftDerivedObj`）、係数拡大と制限は可換（`mapRestrictionIso`）、制限の `i` 次ホモロジーは
もとの複体の `-i` 次ホモロジー（`toChainHomologyIso`。基底変更後も正の次数で零であることを
`baseChange_isZero_X_of_pos` で確かめる）。 -/
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

`a ∈ A` が `V` のすべての元を消すなら、`φ(a)` は `Tor_i^A(C, V)`（`TorAlg φ i V`）のすべての元を
消す（`torAlg_smul_eq_zero`）。`V` が `m` の冪で消えるなら `Tor` も `m C` の冪で消える、という形で
使い、`Tor` が正規化長さ `λ` の定義域（`m C` 冪ねじれ加群）に入ることを保証する
（`IntersectionMultiplicity/NormalizedTor.lean`）。`notes/PLAN.md` §11 の B3。

証明の筋道：`a • 𝟙 V = 0` なので、これを左導来関手で送ったものは零。一方、射影分解 `P` 上の
`a • 𝟙 P` は `a • 𝟙 V` の持ち上げなので、左導来関手の値は `H_i(F(a • 𝟙 P))` で計算できる
（`Functor.leftDerived_map_eq`）。係数拡大とホモロジーがスカラー倍と両立すること
（`BaseChange.lean` の `extendScalars_mapHomologicalComplex_smul`、`Basic.lean` の
`homologyMap_smul`）から、それは `φ(a) • 𝟙` に等しい。よって `φ(a) • 𝟙 = 0`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- `a ∈ A` が `V` のすべての元を消すなら、`φ(a)` は `Tor_i^A(C, V)` のすべての元を消す。
`a • 𝟙 V = 0` を左導来関手で送ると零になる一方、射影分解上の持ち上げ `a • 𝟙 P` で計算すると
`φ(a) • 𝟙` になる（`single_map_smul` で持ち上げの可換性を、`extendScalars_mapHomologicalComplex_smul`
と `homologyMap_smul` でスカラー倍の両立を確かめる）ので、`φ(a) • 𝟙 = 0`。これを元 `x` に適用する。 -/
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
