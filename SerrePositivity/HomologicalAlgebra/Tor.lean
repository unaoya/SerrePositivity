module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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

Mathlib の `Tor` は第 2 変数で導来する。第 1 変数で導来した `Tor'` との比較は
現在の Mathlib に未整備であり、このファイルの計算も第 2 変数の分解による。
`TorSymmetry.lean` では射影的な被覆に沿う次数の帰納法により、両変数を交換した
Tor の線形同値を構成している。高次の同値の自然性は、この構成ではまだ主張しない。
論文で `Tor_i^A(V, C)` と書かれるものは、ここでは `TorAlg φ i V`（`V` を分解）である。

## 内容

通常の Tor について、`torModuleZeroEquiv` が零次とテンソル積の比較、
`torModuleIsoCochain` が任意の第2変数の射影分解による計算を与える。
`ordinaryTorIso` は代数係数のホモロジーの係数制限と通常の Tor を比較する。

後半では `TorAlg` について次を示す。線形同値な加群の `Tor` は線形同値（`torAlgCongr`）、
平坦な第1変数の高次 Tor は零（`torModule_subsingleton_of_flat`）。
零加群の `Tor` は零（`torAlg_subsingleton`、`torModule_subsingleton_left`）、`Tor` は ℤ 添字 cochain 複体の分解で計算できる
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

open MonoidalCategory in
/-- `Tor₀^R(M,N)` は通常のテンソル積と線形同値である。
テンソル関手は左随伴なので右完全であり、Mathlib の `leftDerivedZeroIsoSelf` を適用する。 -/
noncomputable def torModuleZeroEquiv (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : TorModule R 0 M N ≃ₗ[R] TensorProduct R M N :=
  ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf).app
    (ModuleCat.of R N)).toLinearEquiv

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

/-- 零加群の Tor はすべての次数で零である。
左導来関手は加法的なので零対象を零対象に送る。 -/
lemma torAlg_subsingleton (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V] [Subsingleton V] :
    Subsingleton (TorAlg φ i V) := by
  exact ModuleCat.subsingleton_of_isZero
    (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of A V)))

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
  leftDerivedIsoCochain (ModuleCat.extendScalars.{u, u, u} φ) h i

end SerrePositivity

end

/-!
## `Tor` と消去イデアル

`a ∈ A` が `V` のすべての元を消すなら、`φ(a)` は `Tor_i^A(C, V)`（`TorAlg φ i V`）のすべての元を
消す（`torAlg_smul_eq_zero`）。`V` が `m` の冪で消えるなら `Tor` も `m C` の冪で消える、という形で
使い、`Tor` が正規化長さ `λ` の定義域（`m C` 冪ねじれ加群）に入ることを保証する
（`IntersectionMultiplicity/NormalizedTor.lean`）。`notes/PLAN.md` §11 の B3。

証明には `Resolution.lean` の一般定理 `leftDerived_smul_eq_zero` を用いる。
加法的関手が射のスカラー倍と両立すれば、その左導来関手も両立するため、
`a • 𝟙 V = 0` から導来関手の値で `φ(a) • 𝟙 = 0` が従う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- `a ∈ A` が `V` を消すなら、`φ(a)` はすべての `Tor_i^A(C, V)` を消す。
係数拡大のスカラー倍との両立を、一般の左導来関手の零化の定理に適用する。 -/
theorem torAlg_smul_eq_zero (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V] (a : A)
    (ha : ∀ v : V, a • v = 0) (x : TorAlg φ i V) : φ a • x = 0 := by
  exact leftDerived_smul_eq_zero φ (ModuleCat.extendScalars φ)
    (fun a f => extendScalars_map_smul φ f a) i (ModuleCat.of A V) a ha x

end SerrePositivity

end

/-!
## 通常の `Tor` と係数拡大した分解の比較

通常の長さを測るときに使う比較同型を、Mathlib の導来関手の計算から構成する。
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory TensorProduct

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency false in
/-- 係数拡大後に係数を制限する関手は、`T ⊗[R] -` と自然同型である。
係数制限で入るスカラー作用を、既存の `R` 代数構造による作用と同一視する。 -/
noncomputable def extendRestrictScalarsTensorIso :
    ModuleCat.extendScalars (algebraMap R T) ⋙ ModuleCat.restrictScalars (algebraMap R T) ≅
      (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R T) :=
  NatIso.ofComponents (fun M => by
    let T' := (ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)
    let eT : T' ≃ₗ[R] T :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun x => rfl
        right_inv := fun x => rfl
        map_add' := fun x y => rfl
        map_smul' := fun r t => by
          dsimp [T', ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] at t ⊢
          exact (Algebra.smul_def r t).symm }
    let e : ((ModuleCat.restrictScalars (algebraMap R T)).obj
        ((ModuleCat.extendScalars (algebraMap R T)).obj M)) ≃ₗ[R] (T' ⊗[R] M) :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun x => rfl
        right_inv := fun x => rfl
        map_add' := fun x y => rfl
        map_smul' := fun r x => by
          induction x using TensorProduct.inductionOn with
          | tmul t m => rfl
          | add x y hx hy => simp_all only [smul_add] }
    exact (e.trans (TensorProduct.congr eT (LinearEquiv.refl R M))).toModuleIso)
    (by
      intro M N f
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul t m => rfl
      | add x y hx hy => simp_all only [map_add])

/-- 通常の `Tor_i^R(M, N)` を、第2変数 `N` の任意の射影コチェイン分解で計算する。
`M` は任意の加群でよく、代数構造は必要ない。Mathlib のテンソル関手の左導来関手に
`leftDerivedIsoCochain` を適用する。 -/
noncomputable def torModuleIsoCochain (M : Type u) [AddCommGroup M] [Module R M]
    {N : ModuleCat.{u} R} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : IsResolutionOf K N) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj N ≅
      HomologicalComplex.homology
        ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).mapHomologicalComplex _).obj K)
        (-(i : ℤ)) :=
  leftDerivedIsoCochain ((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)) h i

/-- 射影的なコチェイン分解を `T` に係数拡大したホモロジーは、
係数を `R` に制限すると通常の `Tor_i^R(T, M)` と線形同値になる。
係数制限によるホモロジーの保存、テンソル関手の同一視、分解による左導来関手の計算を使う。
Noether 性、局所性、有限生成性、有界性は不要である。 -/
noncomputable def ordinaryTorIso (M : Type u) [AddCommGroup M] [Module R M]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsResolutionOf F (ModuleCat.of R M)) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap R T)).obj
        ((baseChange (algebraMap R T) F).homology (-(i : ℤ)))) ≃ₗ[R] TorModule R i T M := by
  let U := ModuleCat.restrictScalars (algebraMap R T)
  let e := (Functor.mapHomologicalComplexCompIso (extendRestrictScalarsTensorIso (R := R) (T := T))
    (ComplexShape.up ℤ)).app F
  exact ((((baseChange (algebraMap R T) F).sc (-(i : ℤ))).mapHomologyIso U).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso e ≪≫
    (torModuleIsoCochain T hF i).symm).toLinearEquiv

/-- 第1変数を消す元は通常の Tor も消す。
テンソルした分解の各項がその元で消え、ホモロジーは項の部分商だからである。 -/
theorem annihilator_le_torModule_left (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Module.annihilator R M ≤ Module.annihilator R (TorModule R i M N) := by
  let P := projectiveResolution (ModuleCat.of R N)
  let F := (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)
  let K := (F.mapHomologicalComplex _).obj P.complex
  change Module.annihilator R M ≤ Module.annihilator R ((F.leftDerived i).obj (ModuleCat.of R N))
  rw [(P.isoLeftDerivedObj F i).toLinearEquiv.annihilator_eq]
  apply le_trans ?_ (annihilator_le_homology K i)
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  change a • (x : M ⊗[R] P.complex.X i) = 0
  induction x using TensorProduct.inductionOn with
  | tmul m n => rw [TensorProduct.smul_tmul', ha m, zero_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- 第2変数を消す元は通常の Tor も消す。
テンソル関手のスカラー倍との両立を左導来関手へ移して得る。 -/
theorem annihilator_le_torModule_right (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Module.annihilator R N ≤ Module.annihilator R (TorModule R i M N) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  apply leftDerived_smul_eq_zero (RingHom.id R)
    ((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)) ?_ i (ModuleCat.of R N) a ha
  intro X Y a f
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul m x => exact TensorProduct.tmul_smul a m (f x)
  | add x y hx hy => simp_all only [map_add]

end SerrePositivity

end

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 平坦な第1変数に対する正次数の Tor は零。テンソル関手が完全なので、
第2変数の射影分解の消えるホモロジーをそのまま保つ。Tor の対称性は使わない。 -/
lemma torModule_subsingleton_of_flat (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] (i : ℕ) :
    Subsingleton (TorModule R (i + 1) M N) := by
  let P := projectiveResolution (ModuleCat.of R N)
  let G := tensorLeft (ModuleCat.of R M)
  apply ModuleCat.subsingleton_of_isZero
  apply IsZero.of_iso _ (P.isoLeftDerivedObj G (i + 1))
  apply IsZero.of_iso _ ((P.complex.sc (i + 1)).mapHomologyIso G)
  exact G.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (P.complex_exactAt_succ i))

/-- 第1変数が零加群ならすべての Tor は零。0 次は通常のテンソル積、
正次数は零加群の平坦性による。 -/
lemma torModule_subsingleton_left (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton M] (i : ℕ) :
    Subsingleton (TorModule R i M N) := by
  cases i with
  | zero => exact (torModuleZeroEquiv R M N).injective.subsingleton
  | succ i => exact torModule_subsingleton_of_flat (R := R) M N i

end SerrePositivity

end
