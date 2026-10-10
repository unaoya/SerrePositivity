module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# 複体についての基本補題

## 概要

このプロジェクトで扱う複体は、可換環 `R` 上の加群の圏 `ModuleCat R` における ℤ 添字の cochain 複体
`CochainComplex (ModuleCat R) ℤ` である。このファイルには、そうした複体について繰り返し使う
小さな補題を集める。どれも標準的な事実で Mathlib の一般論からすぐに出るが、この形の主張が
Mathlib にないので、一度だけここで用意しておく。

## 内容

前半は零性とスカラー倍について。

- `isZero_homology_of_isZero_X`：ある次数の項が零ならその次数のホモロジーも零（任意のアーベル圏）。
- `isZero_of_isZero_X`：すべての項が零なら複体そのものが零対象。
- `projective_of_free`：自由加群は `ModuleCat R` の射影対象。項が自由な複体を射影加群の複体として
  扱う（K 射影性による持ち上げ）ために使う。
- `smulId a K = a • 𝟙 K`：複体 `K` の `a` 倍写像。Koszul 複体（`Cone(x • 𝟙 K)` の反復）の定義と、
  台の条件（`a^v • 𝟙 P` が零ホモトピック）の記述に使う。
- `homologyMap_smul`・`single_map_smul`：鎖写像の `a` 倍はホモロジーの射の `a` 倍を誘導し、
  一つの次数に集中した複体への埋め込み `single` もスカラー倍と両立する。添字の形 `c` は任意。

後半は項の有限自由性について。

- 零対象は自由かつ有限生成（`isZero_moduleCat_free`、`isZero_moduleCat_finite`）。
- 二つの有限自由加群の直和は有限自由（`free_finite_biprod`）。
- 写像錐の `i` 次の項は `X^{i+1} ⊕ Y^i` なので、`X`、`Y` の項が有限自由なら写像錐の項も有限自由
  （`mappingCone_free_finite`）。台つき完全複体が写像錐で閉じていること
  （`PerfectComplex/Closure.lean`）の根拠になる。
- Noether 環上では、各項が有限生成な複体のホモロジーも有限生成（`homology_moduleFinite`）。
  台つき複体のホモロジーが有限長であること（`PerfectComplex/OrdinaryEuler.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-- ある次数 `i` の項 `K.X i` が零対象なら、`i` 次のホモロジー `K.homology i` も零対象である。
任意のアーベル圏の、任意の添字の形の複体について成り立つ。有界な複体について、範囲外の次数で
ホモロジーが消えることを言うのに繰り返し使う。 -/
lemma isZero_homology_of_isZero_X {C : Type*} [Category* C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) (h : IsZero (K.X i)) :
    IsZero (K.homology i) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (ShortComplex.exact_of_isZero_X₂ _ h)

variable {R : Type u} [CommRing R]

/-- すべての項が零対象なら、複体 `P` 自身が複体の圏の零対象である。複体の射は各次数の成分で
決まるので、恒等射が零射に等しいことを成分ごとに確かめればよい。`K₀` で零複体の類が `0` である
ことを示すとき（`PerfectComplex/K0.lean`）に使う。 -/
lemma isZero_of_isZero_X {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : ∀ i, IsZero (P.X i)) :
    IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun i ↦ (h i).eq_of_src _ _

/-- 自由 `R` 加群 `M` は、加群圏 `ModuleCat R` の対象として射影的である。Mathlib では加群の
射影性 `Module.Projective` と圏論的な射影性 `CategoryTheory.Projective` が別の概念なので、
「自由なら加群として射影的」「加群として射影的なら圏論的に射影的」の二段で移す。項が自由な
複体を K 射影的な複体として扱うとき（`KProjectiveLift.lean`、`CommutativeAlgebra/Truncate.lean`、
`PerfectComplex/KoszulGeneration.lean`）に使う。 -/
lemma projective_of_free {M : ModuleCat.{u} R} (h : Module.Free R M) : Projective M := by
  have : Module.Projective R M := Module.Projective.of_free
  exact M.projective_of_categoryTheory_projective

/-- 複体 `K` の自己射 `a • 𝟙 K`、すなわち各次数で `a` 倍する鎖写像。Koszul 複体は
`Cone(x_n • 𝟙 K(x_1, …, x_{n-1}))` の反復として定義する（`CommutativeAlgebra/Koszul.lean`）ので、
その構成要素になる。`a • 𝟙 K` と書く代わりに名前を付けるのは、写像錐の引数として現れたときに
式を読みやすくするためで、中身は定義どおり `a • 𝟙 K` である。 -/
noncomputable def smulId (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) : K ⟶ K :=
  a • 𝟙 K

section shape

variable {ι : Type*} {c : ComplexShape ι}

/-- 鎖写像のスカラー倍 `a • f` がホモロジーに誘導する射は、`f` が誘導する射の `a` 倍である。
添字の形 `c` は任意。ホモロジーは各次数の短複体 `K.sc i` から関手的に定まるので、短複体の
ホモロジー射がスカラー倍と両立すること（Mathlib の `ShortComplex.homologyMap_smul`）に帰着する。

特に `smulId a K = a • 𝟙 K` はホモロジー上で `a` 倍として働く。これが Koszul 複体の完全性
（`CommutativeAlgebra/KoszulResolution.lean`）、Tor の消去イデアル（`Tor.lean`）、台をもつ複体の
ホモロジーの零化（`PerfectComplex/Support.lean`）の計算の出発点になる。 -/
lemma homologyMap_smul {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (a : R)
    (i : ι) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  have : (HomologicalComplex.shortComplexFunctor _ _ i).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor _ _ i).map f := by
    ext <;> rfl
  simp only [HomologicalComplex.homologyMap, this, ShortComplex.homologyMap_smul]
  rfl

/-- 一つの次数 `j` に集中した複体への埋め込み関手 `single` は、射のスカラー倍を保つ。
`j` 次の成分は `r • f` そのもの、他の次数の成分は零対象の間の射なので自動的に一致する。
Tor の消去イデアルの計算（`Tor.lean` の `torAlg_smul_eq_zero`）で、加群の射 `a • 𝟙 V` を
射影分解の射 `a • 𝟙 P` で持ち上げるときに使う。 -/
lemma single_map_smul [DecidableEq ι] (j : ι) {X Y : ModuleCat.{u} R} (r : R) (f : X ⟶ Y) :
    (HomologicalComplex.single (ModuleCat.{u} R) c j).map (r • f) =
      r • (HomologicalComplex.single (ModuleCat.{u} R) c j).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = j
  · subst h
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X c j X i h).eq_of_src _ _

end shape

end SerrePositivity

end

/-!
## 複体の項の自由性・有限性

零対象、有限直和、写像錐の項が有限自由であること、および Noether 環上で各項が有限生成な複体の
ホモロジーが有限生成であること。台つき完全複体の定義 `IsPerfectSupported`（各項が有限自由）が
写像錐で閉じていること（`PerfectComplex/Closure.lean`）と、そのホモロジーが有限長であること
（`PerfectComplex/OrdinaryEuler.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 加群圏の零対象は自由加群である（空の基底をもつ）。「零対象であること」と「台集合が一点である
こと」の同値（`ModuleCat.isZero_iff_subsingleton`）を経由して、一点の加群が自由であるという
Mathlib のインスタンスに帰着する。 -/
lemma isZero_moduleCat_free {M : ModuleCat.{u} R} (h : IsZero M) : Module.Free R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

/-- 加群圏の零対象は有限生成である。`isZero_moduleCat_free` と同じく、台集合が一点であることに
言い換えてから Mathlib のインスタンスに帰着する。 -/
lemma isZero_moduleCat_finite {M : ModuleCat.{u} R} (h : IsZero M) : Module.Finite R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

/-- 二つの有限自由加群 `M`、`N` の圏論的直和 `M ⊞ N` は有限自由である。`M ⊞ N` は直積
`M × N` と線形同型（`ModuleCat.biprodIsoProd`）なので、直積が有限自由であるという Mathlib の
結果を同型に沿って移す。 -/
lemma free_finite_biprod (M N : ModuleCat.{u} R) [Module.Free R M] [Module.Free R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.Free R (M ⊞ N : ModuleCat.{u} R) ∧ Module.Finite R (M ⊞ N : ModuleCat.{u} R) := by
  let e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) := (ModuleCat.biprodIsoProd M N).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- 写像錐 `Cone(f)` の `i` 次の項は `X^{i+1} ⊕ Y^i` なので、`X^{i+1}` と `Y^i` が有限自由なら
`Cone(f)^i` も有限自由である。Mathlib の `homotopyCofiber.XIsoBiprod` で項を直和と同一視し、
`free_finite_biprod` を使う。台つき完全複体が写像錐で閉じていること
（`PerfectComplex/Closure.lean` の `IsPerfectSupported.mappingCone`）に使う。 -/
lemma mappingCone_free_finite {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) (i : ℤ)
    [Module.Free R (X.X (i + 1))] [Module.Free R (Y.X i)]
    [Module.Finite R (X.X (i + 1))] [Module.Finite R (Y.X i)] :
    Module.Free R ((CochainComplex.mappingCone f).X i) ∧
      Module.Finite R ((CochainComplex.mappingCone f).X i) := by
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).toLinearEquiv
  obtain ⟨h1, h2⟩ := free_finite_biprod (X.X (i + 1)) (Y.X i)
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- Noether 環 `R` 上で、複体 `P` の `i` 次の項が有限生成なら、`i` 次のホモロジー `H^i(P)` も
有限生成である。ホモロジーはサイクル（`P^i` の部分加群）を境界（その部分加群）で割ったもので、
Noether 環上では有限生成加群の部分加群も商も有限生成だからである。Mathlib の `ModuleCat` 用の
ホモロジーの具体的な表示（`moduleCatHomologyIso`）で核と像の商に書き直してから、インスタンスで
片づける。台つき完全複体のホモロジーが有限長であること（`PerfectComplex/OrdinaryEuler.lean`）と、
ホモロジーの台の言い換え（`PerfectComplex/Support.lean`）で使う。 -/
lemma homology_moduleFinite [IsNoetherianRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [Module.Finite R (P.X i)] : Module.Finite R (P.homology i) := by
  let S := P.sc i
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (P.X i))
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

end SerrePositivity

end
