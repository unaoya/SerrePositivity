module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # 加群の cochain 複体の基本補題

## 概要

可換環 R 上の ℤ 添字 cochain 複体 `CochainComplex (ModuleCat R) ℤ` について繰り返し使う小さな補題を集める：項が零なら複体・ホモロジーが零、スカラー倍 `smulId` とホモロジー・`single` との両立、零化イデアルがホモロジーを零化すること、有限自由な項の直和・写像錐、有限生成なホモロジー、短複体の積、有限双積、次数ごとの写像の核への持ち上げ、二つの生成元で指定する二項スカラー複体からの鎖写像。

## 方針

どれも Mathlib の一般論からすぐ出るが、この形の主張が Mathlib にないので一度だけ用意する。双積の instance は `HasFiniteBiproducts.of_hasFiniteProducts` から。

## 規約

`isZero_homology_of_isZero_X`・`projective_of_free`・`isZero_moduleCat_free` は Mathlib の `ShortComplex.isZero_homology_of_isZero_X₂`・`ModuleCat.projective_of_free`・`Module.Free.of_subsingleton` で置き換える候補（refactor-plan §3.2.2）。

## 使われ方

HomologicalAlgebra・PerfectComplex・KTheory の全体。
-/

@[expose] public noncomputable section

universe u

section BasicPart

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
`Cone(x_n • 𝟙 K(x_1, …, x_{n-1}))` の反復として定義する（`CommutativeAlgebra/Koszul/Basic.lean`）ので、
その構成要素になる。`a • 𝟙 K` と書く代わりに名前を付けるのは、写像錐の引数として現れたときに
式を読みやすくするためで、中身は定義どおり `a • 𝟙 K` である。 -/
noncomputable def smulId (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) : K ⟶ K :=
  a • 𝟙 K

section shape

variable {ι : Type*} {c : ComplexShape ι}

/-- ホモロジーの零化イデアルは、同じ次数の複体の項の零化イデアルを含む。
サイクルへの単射とホモロジーへの全射を通して、零化イデアルの包含を合成する。 -/
theorem annihilator_le_homology {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    Module.annihilator R (K.X i) ≤ Module.annihilator R (K.homology i) :=
  ((K.iCycles i).hom.annihilator_le_of_injective
    ((ModuleCat.mono_iff_injective _).mp inferInstance)).trans
    ((K.homologyπ i).hom.annihilator_le_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- 鎖写像のスカラー倍 `a • f` がホモロジーに誘導する射は、`f` が誘導する射の `a` 倍である。
添字の形 `c` は任意。ホモロジーは各次数の短複体 `K.sc i` から関手的に定まるので、短複体の
ホモロジー射がスカラー倍と両立すること（Mathlib の `ShortComplex.homologyMap_smul`）に帰着する。

特に `smulId a K = a • 𝟙 K` はホモロジー上で `a` 倍として働く。これが Koszul 複体の完全性
（`CommutativeAlgebra/Koszul/Resolution.lean`）、Tor の消去イデアル（`Tor.lean`）、台をもつ複体の
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


/-!
## 複体の項の自由性・有限性

零対象、有限直和、写像錐の項が有限自由であること、および Noether 環上で各項が有限生成な複体の
ホモロジーが有限生成であること。台つき完全複体の定義 `IsPerfectSupported`（各項が有限自由）が
写像錐で閉じていること（`PerfectComplex/Closure.lean`）と、そのホモロジーが有限長であること
（`PerfectComplex/OrdinaryEuler.lean`）に使う。
-/


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

/-- 二つの加群の短複体の項ごとの直積。 -/
def moduleCatShortComplexProd (S T : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (S.f.hom.prodMap T.f.hom) (S.g.hom.prodMap T.g.hom)
    (by ext x <;> simp [S.moduleCat_zero_apply, T.moduleCat_zero_apply])

/-- 短完全列の有限直積は短完全である。核と像の等式、単射性、全射性を成分ごとに確認する。 -/
lemma moduleCatShortComplexProd_shortExact {S T : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hT : T.ShortExact) : (moduleCatShortComplexProd S T).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (hS.moduleCat_injective_f.prodMap hT.moduleCat_injective_f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (hS.moduleCat_surjective_g.prodMap hT.moduleCat_surjective_g)
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hs : S.g x.1 = 0 := congrArg Prod.fst hx
    have ht : T.g x.2 = 0 := congrArg Prod.snd hx
    obtain ⟨y, hy⟩ := S.moduleCat_exact_iff.mp hS.exact _ hs
    obtain ⟨z, hz⟩ := T.moduleCat_exact_iff.mp hT.exact _ ht
    exact ⟨(y,z), Prod.ext hy hz⟩

/-- 加群の圏論的直和と直積の標準同型は、各成分の射と両立する。 -/
lemma moduleCat_prodMap_biprodIsoProd_inv {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ModuleCat.ofHom (f.hom.prodMap g.hom) ≫ (ModuleCat.biprodIsoProd M' N').inv =
      (ModuleCat.biprodIsoProd M N).inv ≫ biprod.map f g := by
  apply biprod.hom_ext
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.map_fst,
      reassoc_of% ModuleCat.biprodIsoProd_inv_comp_fst M N]
    rfl
  · simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.map_snd,
      reassoc_of% ModuleCat.biprodIsoProd_inv_comp_snd M N]
    rfl

/-- 有限自由加群に対する基底の個数による帰納法。零加群と環で成り立ち、
同型と二項の直積で保たれる性質は、すべての有限自由加群で成り立つ。 -/
lemma finiteFree_module_induction (F : ModuleCat.{u} R → Prop)
    (hzero : ∀ M, IsZero M → F M) (hR : F (ModuleCat.of R R))
    (hiso : ∀ {M N : ModuleCat.{u} R}, (M ≅ N) → F M → F N)
    (hprod : ∀ M N : ModuleCat.{u} R, F M → F N → F (ModuleCat.of R (M × N)))
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] : F M := by
  have hfin : ∀ n : ℕ, F (ModuleCat.of R (Fin n → R)) := by
    intro n
    induction n with
    | zero => exact hzero _ (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    | succ n ih =>
      let e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
      exact hiso e.symm.toModuleIso (hprod _ _ hR ih)
  let b := Module.Free.chooseBasis R M
  let e := b.equivFun ≪≫ₗ LinearEquiv.funCongrLeft R R
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R M)).symm
  exact hiso e.symm.toModuleIso (hfin _)

/-- 下端 `a` より下が零の複体から、その `a` 次の項だけを残した単一複体への自然な射。 -/
noncomputable def bottomProjection (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (P.X i)) :
    P ⟶ (HomologicalComplex.single _ _ a).obj (P.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi ↦ by
    have hia : i < a := by
      have : i + 1 = a := hi
      omega
    exact (ha i hia).eq_of_src _ _)

/-- 下端への射は各次数で全射なので、複体の圏でも全射である。 -/
lemma bottomProjection_epi (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (P.X i)) : Epi (bottomProjection P a ha) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  by_cases hi : i = a
  · subst i
    dsimp [bottomProjection]
    rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (P.X a) i hi).epi _

/-- 下端への射の核は、その下端の次数では零となる。 -/
lemma bottomProjection_kernel_isZero (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (P.X i)) :
    IsZero ((kernel (bottomProjection P a ha)).X a) := by
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) a
  have : Mono ((bottomProjection P a ha).f a) := by
    dsimp [bottomProjection]
    rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    infer_instance
  have : Mono (E.map (bottomProjection P a ha)) :=
    inferInstanceAs (Mono ((bottomProjection P a ha).f a))
  exact (isZero_zero _).of_iso
    (PreservesKernel.iso E (bottomProjection P a ha) ≪≫ kernel.ofMono _)

/-- 下端以外の次数では、下端への射の核の項は元の項と同型である。 -/
noncomputable def bottomProjectionKernelXIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (ha : ∀ i, i < a → IsZero (P.X i)) (i : ℤ) (hi : i ≠ a) :
    (kernel (bottomProjection P a ha)).X i ≅ P.X i := by
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have hzero : E.map (bottomProjection P a ha) = 0 :=
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (P.X a) i hi).eq_of_tgt _ _
  have := kernel.ι_of_zero hzero
  exact PreservesKernel.iso E (bottomProjection P a ha) ≪≫ asIso (kernel.ι _)

/-- 有界な有限自由複体に対する、項による有限フィルトレーションの帰納法。
零複体と有限自由加群の単一複体で成り立ち、短完全列の両端から中央へ移る性質は、
任意の有界有限自由複体で成り立つ。下端の項への射の核は一段短く、残る項は元の項と
同型なので、係数環の Noether 性や局所性は不要である。 -/
lemma boundedFiniteFree_induction
    (F : CochainComplex (ModuleCat.{u} R) ℤ → Prop)
    (hzero : ∀ P, IsZero P → F P)
    (hsingle : ∀ (a : ℤ) (M : ModuleCat.{u} R), Module.Free R M → Module.Finite R M →
      F ((HomologicalComplex.single _ _ a).obj M))
    (hext : ∀ S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ),
      S.ShortExact → F S.X₁ → F S.X₃ → F S.X₂)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ i, Module.Free R (P.X i)) (hfinite : ∀ i, Module.Finite R (P.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) : F P := by
  suffices aux : ∀ (n : ℕ) (a : ℤ) (Q : CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ i, Module.Free R (Q.X i)) → (∀ i, Module.Finite R (Q.X i)) →
      (∀ i, (i < a ∨ a + n ≤ i) → IsZero (Q.X i)) → F Q by
    obtain ⟨a, b, hb⟩ := hbounded
    exact aux (b - a + 1).toNat a P hfree hfinite (fun i hi ↦ hb i (by
      rcases hi with hi | hi
      · exact Or.inl hi
      · right; omega))
  intro n
  induction n with
  | zero =>
    intro a Q _ _ hb
    apply hzero Q
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.Hom.ext
    funext i
    exact (hb i (by omega)).eq_of_src _ _
  | succ n ih =>
    intro a Q hfree hfinite hb
    let ha := fun i (hi : i < a) ↦ hb i (Or.inl hi)
    let π := bottomProjection Q a ha
    let Q' := kernel π
    have hepi : Epi π := bottomProjection_epi Q a ha
    let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
      ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    apply hext S hS
    · apply ih (a + 1) Q'
      · intro i
        by_cases hi : i = a
        · subst i
          exact isZero_moduleCat_free (bottomProjection_kernel_isZero Q a ha)
        · have := hfree i
          exact Module.Free.of_equiv (bottomProjectionKernelXIso Q a ha i hi).symm.toLinearEquiv
      · intro i
        by_cases hi : i = a
        · subst i
          exact isZero_moduleCat_finite (bottomProjection_kernel_isZero Q a ha)
        · have := hfinite i
          exact Module.Finite.equiv (bottomProjectionKernelXIso Q a ha i hi).symm.toLinearEquiv
      · intro i hi
        by_cases hia : i = a
        · subst i
          exact bottomProjection_kernel_isZero Q a ha
        · exact (hb i (by omega)).of_iso (bottomProjectionKernelXIso Q a ha i hia)
    · exact hsingle a (Q.X a) (hfree a) (hfinite a)

end SerrePositivity


end BasicPart

section CochainBiproductPart

namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R]

instance (priority := 100) cochainComplexHasFiniteBiproducts :
    HasFiniteBiproducts (CochainComplex (ModuleCat.{u} R) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end SerrePositivity

end CochainBiproductPart

section CochainKernelLiftPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Evaluation preserves exactness of the kernel sequence, so a graded map can be lifted. -/
def cochainKernelLiftX {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (n : ℤ) {W : ModuleCat.{u} R} (v : W ⟶ P.X n)
    (hv : v ≫ f.f n = 0) : W ⟶ (kernel f).X n := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let S' := S.map (eval _ _ n)
  have : Mono S'.f := by
    change Mono ((kernel.ι f).f n)
    infer_instance
  have he : S'.Exact := (ShortComplex.exact_kernel f).map (eval _ _ n)
  exact he.lift v hv

@[reassoc]
lemma cochainKernelLiftX_inclusion {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (n : ℤ) {W : ModuleCat.{u} R} (v : W ⟶ P.X n)
    (hv : v ≫ f.f n = 0) :
    cochainKernelLiftX f n v hv ≫ (kernel.ι f).f n = v := by
  dsimp [cochainKernelLiftX]
  exact Fork.IsLimit.lift_ι _

/-- Compute a component of a graded kernel lift through a monic comparison square. -/
lemma cochainKernelLiftX_comp_eq
    {P Q A B : CochainComplex (ModuleCat.{u} R) ℤ} {f : P ⟶ Q} {n : ℤ}
    {W : ModuleCat.{u} R} {v : W ⟶ P.X n} {hv : v ≫ f.f n = 0}
    {m : kernel f ⟶ A} {i : A ⟶ B} [Mono (i.f n)] {g : P ⟶ B}
    (hm : m ≫ i = kernel.ι f ≫ g) {t : W ⟶ A.X n}
    (ht : v ≫ g.f n = t ≫ i.f n) : cochainKernelLiftX f n v hv ≫ m.f n = t := by
  apply (cancel_mono (i.f n)).mp
  rw [Category.assoc, ← HomologicalComplex.comp_f, hm, HomologicalComplex.comp_f,
    cochainKernelLiftX_inclusion_assoc]
  exact ht

lemma cochainBiprodDegree_hom_ext (A B : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) {W : ModuleCat.{u} R} {f g : W ⟶ (A ⊞ B).X n}
    (hf : f ≫ (biprod.fst : A ⊞ B ⟶ A).f n = g ≫ (biprod.fst : A ⊞ B ⟶ A).f n)
    (hg : f ≫ (biprod.snd : A ⊞ B ⟶ B).f n = g ≫ (biprod.snd : A ⊞ B ⟶ B).f n) : f = g := by
  apply (isLimitOfPreserves (eval (ModuleCat.{u} R) (.up ℤ) n)
    (BinaryBiproduct.isLimit A B)).hom_ext
  rintro ⟨j⟩
  cases j
  · exact hf
  · exact hg

end SerrePositivity

end CochainKernelLiftPart

section CochainTwoTermScalarMapPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (l u : ℤ)
variable (eL : P.X l ≅ ModuleCat.of R R) (eU : P.X u ≅ ModuleCat.of R R)
variable (fL : ModuleCat.of R R ⟶ Q.X l) (fU : ModuleCat.of R R ⟶ Q.X u)

def cochainTwoTermScalarMapX (n : ℤ) : P.X n ⟶ Q.X n :=
  if h : n = l then (P.XIsoOfEq h).hom ≫ eL.hom ≫ fL ≫ (Q.XIsoOfEq h).inv
  else if h : n = u then (P.XIsoOfEq h).hom ≫ eU.hom ≫ fU ≫ (Q.XIsoOfEq h).inv
  else 0

@[simp]
lemma cochainTwoTermScalarMapX_lower :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU l = eL.hom ≫ fL := by
  simp [cochainTwoTermScalarMapX]

@[simp]
lemma cochainTwoTermScalarMapX_upper (hne : u ≠ l) :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU u = eU.hom ≫ fU := by
  simp [cochainTwoTermScalarMapX, hne]

variable (hlu : l + 1 = u) (hp : ∀ n, n ≠ l ∧ n ≠ u → IsZero (P.X n)) (r : R)
variable (hd : eL.inv ≫ P.d l u = r • eU.inv)
variable (hL : fL ≫ Q.d l u = r • fU) (hU : fU ≫ Q.d u (u + 1) = 0)

include hlu hp hd hL hU in
lemma cochainTwoTermScalarMapX_comm (n m : ℤ) (h : n + 1 = m) :
    cochainTwoTermScalarMapX P Q l u eL eU fL fU n ≫ Q.d n m =
      P.d n m ≫ cochainTwoTermScalarMapX P Q l u eL eU fL fU m := by
  subst m
  by_cases hnL : n = l
  · subst n
    rw [hlu]
    apply (cancel_epi eL.inv).mp
    simp only [cochainTwoTermScalarMapX_lower,
      cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [hL, ← Category.assoc eL.inv, hd, Linear.smul_comp, Iso.inv_hom_id_assoc]
  · by_cases hnU : n = u
    · subst n
      have hdU : P.d u (u + 1) = 0 := (hp (u + 1) (by omega)).eq_of_tgt _ _
      rw [hdU, zero_comp, cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
        Category.assoc, hU, comp_zero]
    · exact (hp n ⟨hnL, hnU⟩).eq_of_src _ _

def cochainTwoTermScalarMap : P ⟶ Q where
  f := cochainTwoTermScalarMapX P Q l u eL eU fL fU
  comm' n m h := cochainTwoTermScalarMapX_comm P Q l u eL eU fL fU hlu hp r hd hL hU n m h

include hlu hp hd hL hU in
lemma cochainTwoTermScalarMap_eigen (τ : Q ⟶ Q) (c : R)
    (hcL : fL ≫ τ.f l = c • fL) (hcU : fU ≫ τ.f u = c • fU) :
    cochainTwoTermScalarMap P Q l u eL eU fL fU hlu hp r hd hL hU ≫ τ =
      c • cochainTwoTermScalarMap P Q l u eL eU fL fU hlu hp r hd hL hU := by
  apply HomologicalComplex.Hom.ext
  funext n
  change cochainTwoTermScalarMapX P Q l u eL eU fL fU n ≫ τ.f n =
    c • cochainTwoTermScalarMapX P Q l u eL eU fL fU n
  by_cases hnL : n = l
  · subst n
    rw [cochainTwoTermScalarMapX_lower, Category.assoc, hcL, Linear.comp_smul]
  · by_cases hnU : n = u
    · subst n
      rw [cochainTwoTermScalarMapX_upper P Q l u eL eU fL fU (by omega),
        Category.assoc, hcU, Linear.comp_smul]
    · exact (hp n ⟨hnL, hnU⟩).eq_of_src _ _

end SerrePositivity

end CochainTwoTermScalarMapPart
