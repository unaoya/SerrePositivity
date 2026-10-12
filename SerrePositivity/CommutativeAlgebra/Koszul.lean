module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Length
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Koszul 複体

## 概要

可換環 `R` の元の列 `x = (x_0, …, x_{n-1})` の Koszul 複体 `K(x; R)` を定義し、項についての基本的な
性質を示す。Koszul 複体はこのプロジェクトで二つの役割をもつ。

- 正則局所環 `A` の正則パラメータ系 `z` について、`K(z; A)` は剰余体 `k = A/(z)` の有限自由分解で
  ある（`KoszulResolution.lean`）。これにより `Tor_i^A(C, k)` が Koszul ホモロジー `H_i(z; C)` で
  計算でき（論文 (3.9)、Lemma 3.4、Corollary 2.6）、また `K(z)` の類が台つき完全複体の `K₀` を
  生成する（Lemma 3.5b、`PerfectComplex/KoszulGeneration.lean`）。
- `K(z)` は、`z` に台をもつ完全複体の基本例である（`PerfectComplex/Support.lean`）。

## 定義

写像錐の反復で定義する：

- `K(∅) = R`（`0` 次に集中した複体）
- `K(x_0, …, x_n) = Cone(x_n • 𝟙 : K(x_0, …, x_{n-1}) → K(x_0, …, x_{n-1}))`

これは `K(x) ≅ Cone(x_n : K(x') → K(x'))` という標準的な特徴づけそのもので、外積代数による定義は
使わない。最後の元を外側の写像錐にとるので、正則列についての帰納法（`x_n` は `R/(x_0, …, x_{n-1})`
上で正則。Mathlib の `RingTheory.Sequence.IsWeaklyRegular` と同じ向き）にそのまま使える。

## 規約

添字は cochain（`ComplexShape.up ℤ`）で、`K(x)` は `-n, …, 0` 次に乗る。論文は homological に
添字づけしているので、`H_i(x; M)` は cochain の `-i` 次のホモロジーである（`koszulHomologySelf x i`）。
係数 `C` の Koszul ホモロジー `H_i(z; C)` は、`z` の像の Koszul 複体 `K(φ z; C)` のホモロジー
`koszulHomologySelf (φ ∘ z) i` で書く。`K(z; A) ⊗_A C ≅ K(φ z; C)` はこのファイルの後半
（`baseChangeKoszulIso`）で示す。

## 内容

- 係数複体に関する Koszul 関手 `koszulFunctor`：加法性、短完全列の保存、シフトとの両立、
  零ホモトピーからの直和因子の構成。
- 項の性質：正の次数と `-n` 次より下で零、各項は有限自由で射影的、正の次数のホモロジーは零。
- `koszulEulerChar A T z`：`A` 上の代数 `T` について、`K(z; T)` のホモロジーを `A` 加群として測った
  Euler 標数 `χ^A(z; T) = Σ (-1)^i ℓ_A(H_i(z; T))`。論文 (3.14) に現れ、正則局所環なら `rank_A T` に
  等しい（Serre の定理。`CommutativeAlgebra/RegularLocalRing.lean` の入力）。
- 基底変更との両立 `K(z; A) ⊗_A C ≅ K(φ z; C)`。

完全性（正則列なら分解）は `KoszulResolution.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 列 `x : Fin n → R` の Koszul 複体 `K(x; R)`。`n` に関する再帰で定義する：空列では `R` を `0` 次に
置いた複体、列を一つ延ばすごとに最後の元 `x (Fin.last n)` 倍の写像錐をとる。`n` 個の元に対して
`-k` 次の項は `R^{C(n,k)}` と同型で、全体で `2^n` 個の自由加群からなる。 -/
noncomputable def koszulComplex : {n : ℕ} → (Fin n → R) → CochainComplex (ModuleCat.{u} R) ℤ
  | 0, _ =>
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)
  | n + 1, x =>
    CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x)))

/-- `K(x; R)` の homological 次数 `i` のホモロジー `H_i(x; R)`、cochain では `-i` 次。論文の係数つきの
Koszul ホモロジー `H_i(z; C)` は、係数拡大した複体 `K(φ z; C)` についてのこれで書く。 -/
noncomputable abbrev koszulHomologySelf {n : ℕ} (x : Fin n → R) (i : ℕ) : Type u :=
  (koszulComplex x).homology (-(i : ℤ))

/-- 空の列の Koszul 複体は、`R` を `0` 次に置いた単一複体である（定義の展開）。 -/
lemma koszulComplex_zero (x : Fin 0 → R) :
    koszulComplex x =
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R) :=
  rfl

/-- 列の末尾に元 `x_n` を加えた Koszul 複体は、それまでの複体の `x_n` 倍写像の写像錐である
（定義の展開）。`n` についての帰納法の各段で、これで書き換えてから写像錐の性質を使う。 -/
lemma koszulComplex_succ {n : ℕ} (x : Fin (n + 1) → R) :
    koszulComplex x =
      CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x))) :=
  rfl

/-! ## 複体を係数とする Koszul 複体と直和因子 -/

/-- 複体 `P` を元 `a` の作用の写像錐に送る関手。射には自然な可換正方形から誘導される
錐の射を対応させる。係数複体を変えたときの Koszul 構成の関手性を表す。 -/
noncomputable def scalarConeFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj P := CochainComplex.mappingCone (smulId a P)
  map {P Q} f := HomologicalComplex.homotopyCofiber.mapArrowHom
    (smulId a P) (smulId a Q) (fun j ↦ ⟨j - 1, by simp⟩)
    (Arrow.homMk f f (by simp [smulId]))
  map_id P := by
    have he : Arrow.homMk (𝟙 P) (𝟙 P) (by simp [smulId]) =
        𝟙 (Arrow.mk (smulId a P)) := by ext <;> rfl
    rw [he]
    exact HomologicalComplex.homotopyCofiber.mapArrowHom_id _ _
  map_comp {P Q S} f g := by
    exact HomologicalComplex.homotopyCofiber.mapArrowHom_comp
      (smulId a P) (smulId a Q) (smulId a S) (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk f f (by simp [smulId])) (Arrow.homMk g g (by simp [smulId]))

section scalarCone

open HomologicalComplex.homotopyCofiber

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 錐の射は左成分では、元の複体の一つ上の次数の射を誘導する。 -/
@[reassoc]
lemma scalarConeFunctor_inl_map (a : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (i : ℤ) :
    inlX (smulId a P) (i + 1) i rfl ≫ ((scalarConeFunctor a).map f).f i =
      f.f (i + 1) ≫ inlX (smulId a Q) (i + 1) i rfl := by
  dsimp only [scalarConeFunctor]
  rw [mapArrowHom, inlX_desc_f _ _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
  simp [Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft,
    inrCompHomotopy_hom _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 錐の射は右成分では、元の複体の同じ次数の射を誘導する。 -/
@[reassoc]
lemma scalarConeFunctor_inr_map (a : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (i : ℤ) :
    inrX (smulId a P) i ≫ ((scalarConeFunctor a).map f).f i =
      f.f i ≫ inrX (smulId a Q) i := by
  dsimp only [scalarConeFunctor]
  rw [mapArrowHom, inrX_desc_f]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- スカラー作用の錐をとる関手は加法的である。 -/
instance scalarConeFunctor_additive (a : R) : (scalarConeFunctor a).Additive where
  map_add {P Q} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ext_from_X (smulId a P) (i + 1) i (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
    · simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add, scalarConeFunctor_inl_map,
        Preadditive.add_comp]
    · simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add, scalarConeFunctor_inr_map,
        Preadditive.add_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 錐の各項を二項の直和と同一視すると、誘導される射は元の射の直和になる。 -/
lemma scalarConeFunctor_map_XIso (a : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (i : ℤ) :
    ((scalarConeFunctor a).map f).f i ≫ (XIsoBiprod (smulId a Q) i (i+1) rfl).hom =
      (XIsoBiprod (smulId a P) i (i+1) rfl).hom ≫ biprod.map (f.f (i+1)) (f.f i) := by
  apply ext_from_X (smulId a P) (i + 1) i (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
  · simp only [scalarConeFunctor_inl_map_assoc,
      inlX_XIsoBiprod_hom, inlX_XIsoBiprod_hom_assoc, biprod.inl_map]
  · simp only [scalarConeFunctor_inr_map_assoc,
      inrX_XIsoBiprod_hom, inrX_XIsoBiprod_hom_assoc, biprod.inr_map]

/-- スカラー作用の錐の項を、元の複体の隣り合う二項の直積と同一視する。 -/
noncomputable def scalarConeXIsoProd (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ((scalarConeFunctor a).obj P).X i ≅ ModuleCat.of R (P.X (i+1) × P.X i) :=
  XIsoBiprod (smulId a P) i (i+1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 錐の項の直積表示は、係数複体の射について自然である。 -/
lemma scalarConeXIsoProd_inv_naturality (a : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (i : ℤ) :
    ModuleCat.ofHom ((f.f (i+1)).hom.prodMap (f.f i).hom) ≫ (scalarConeXIsoProd a Q i).inv =
      (scalarConeXIsoProd a P i).inv ≫ ((scalarConeFunctor a).map f).f i := by
  have hn : biprod.map (f.f (i+1)) (f.f i) ≫ (XIsoBiprod (smulId a Q) i (i+1) rfl).inv =
      (XIsoBiprod (smulId a P) i (i+1) rfl).inv ≫ ((scalarConeFunctor a).map f).f i := by
    apply (cancel_mono (XIsoBiprod (smulId a Q) i (i+1) rfl).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [scalarConeFunctor_map_XIso, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  dsimp only [scalarConeXIsoProd, Iso.trans_inv]
  rw [← Category.assoc, moduleCat_prodMap_biprodIsoProd_inv, Category.assoc, hn, Category.assoc]

/-- スカラー作用の錐をとる関手は短完全列を保つ。各次数では二つの短完全列の直積に帰着する。 -/
lemma scalarConeFunctor_shortExact (a : R)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) :
    (S.map (scalarConeFunctor a)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let S₁ := S.map (HomologicalComplex.eval _ _ (i+1))
  let S₂ := S.map (HomologicalComplex.eval _ _ i)
  have h₁ : S₁.ShortExact := hS.map _
  have h₂ : S₂.ShortExact := hS.map _
  let e : moduleCatShortComplexProd S₁ S₂ ≅
      (S.map (scalarConeFunctor a)).map (HomologicalComplex.eval _ _ i) :=
    ShortComplex.isoMk (scalarConeXIsoProd a S.X₁ i).symm
      (scalarConeXIsoProd a S.X₂ i).symm (scalarConeXIsoProd a S.X₃ i).symm
      (scalarConeXIsoProd_inv_naturality a S.f i).symm
      (scalarConeXIsoProd_inv_naturality a S.g i).symm
  exact ShortComplex.shortExact_of_iso e (moduleCatShortComplexProd_shortExact h₁ h₂)

end scalarCone

/-- 係数複体を変数とする Koszul 関手。各元のスカラー作用の錐をとる関手を合成する。 -/
noncomputable def koszulFunctor : {n : ℕ} → (Fin n → R) →
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ
  | 0, _ => 𝟭 _
  | n + 1, x => koszulFunctor (Fin.init x) ⋙ scalarConeFunctor (x (Fin.last n))

/-- 複体 `P` を係数とする Koszul 複体 `K(x; P)`。Koszul 関手の対象部分であり、
空列では `P`、元を一つ加えるごとにそのスカラー作用の写像錐をとる。 -/
noncomputable abbrev koszulComplexOn {n : ℕ} (x : Fin n → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (koszulFunctor x).obj P

/-- Koszul 関手は加法的である。 -/
instance koszulFunctor_additive {n : ℕ} (x : Fin n → R) : (koszulFunctor x).Additive := by
  induction n with
  | zero => change (𝟭 _).Additive; infer_instance
  | succ n ih =>
    have := ih (Fin.init x)
    change (koszulFunctor (Fin.init x) ⋙ scalarConeFunctor (x (Fin.last n))).Additive
    infer_instance

/-- 係数複体の短完全列は、Koszul 関手を適用した後も短完全である。
列の長さについて帰納し、一段の錐の完全性を反復する。 -/
lemma koszulFunctor_shortExact {n : ℕ} (x : Fin n → R)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) :
    (S.map (koszulFunctor x)).ShortExact := by
  induction n with
  | zero => simpa only [koszulFunctor, ShortComplex.map_id] using hS
  | succ n ih =>
    simpa only [koszulFunctor, ShortComplex.map_comp] using
      scalarConeFunctor_shortExact (x (Fin.last n)) (S.map (koszulFunctor (Fin.init x)))
        (ih (Fin.init x))

/-- Koszul 構成は係数複体のシフトと同型を除いて可換である。
一段ごとに Mathlib の写像錐とシフトの同型を適用する。 -/
noncomputable def koszulComplexOnShiftIso {n : ℕ} (x : Fin n → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) :
    (koszulComplexOn x P)⟦m⟧ ≅ koszulComplexOn x (P⟦m⟧) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    let Q := koszulComplexOn (Fin.init x) P
    have he : (smulId (x (Fin.last n)) Q)⟦m⟧' = smulId (x (Fin.last n)) (Q⟦m⟧) := by
      simp [smulId, Functor.map_smul]
    exact CochainComplex.mappingCone.shiftIso (smulId (x (Fin.last n)) Q) m ≪≫
      eqToIso (by rw [he]; rfl) ≪≫
      (scalarConeFunctor (x (Fin.last n))).mapIso (ih (Fin.init x))


/-- 環を零次に集中させた係数複体に対する Koszul 構成は、通常の Koszul 複体と一致する。 -/
lemma koszulComplexOn_single {n : ℕ} (x : Fin n → R) :
    koszulComplexOn x
      ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R)) = koszulComplex x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CochainComplex.mappingCone _ = CochainComplex.mappingCone _
    exact congrArg (fun Q ↦ CochainComplex.mappingCone (smulId (x (Fin.last n)) Q))
      (ih (Fin.init x))

/-- `a` の作用が零ホモトピックなら、元の複体はその作用の写像錐の直和因子となる。
包含の左逆を零ホモトピーから構成する。 -/
noncomputable def retractScalarCone (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : Homotopy (smulId a P) 0) : Retract P ((scalarConeFunctor a).obj P) where
  i := HomologicalComplex.homotopyCofiber.inr (smulId a P)
  r := HomologicalComplex.homotopyCofiber.desc (smulId a P) (𝟙 P)
    (by simpa using h)
  retract := HomologicalComplex.homotopyCofiber.inr_desc _ _ _

/-- 列の各元が係数複体 `P` に零ホモトピックに作用すれば、`P` は `K(x; P)` の直和因子。
各元の零ホモトピーの間に両立条件は不要である。既に得た分裂を錐関手で送り、
最後の元の作用による分裂と合成して帰納的に構成する。 -/
noncomputable def retractKoszulComplexOn : ∀ {n : ℕ} (x : Fin n → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (_h : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0)), Retract P (koszulComplexOn x P)
  | 0, _, P, _ => Retract.refl P
  | n + 1, x, P, h =>
    (retractScalarCone (x (Fin.last n)) P (h (Fin.last n)).some).trans
      ((retractKoszulComplexOn (Fin.init x) P (fun j ↦ h j.castSucc)).map
        (scalarConeFunctor (x (Fin.last n))))

/-! ## 項の性質 -/

/-- Koszul 複体は正の次数で零。`n` についての帰納法で、写像錐の項 `Cone^i = K'^{i+1} ⊕ K'^i` が
零であることに帰着する。 -/
lemma koszulComplex_isZero_X_of_pos :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), 0 < i → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_pos (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_pos (Fin.init x) i hi⟩

/-- `n` 個の元の Koszul 複体は `-n` 次より下で零。帰納法で、`Cone^i = K'^{i+1} ⊕ K'^i` と、`K'` が
`-(n-1)` 次より下で零であることによる。 -/
lemma koszulComplex_isZero_X_of_lt :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), i < -(n : ℤ) → IsZero ((koszulComplex x).X i)
  | 0, x, i, hi => by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  | n + 1, x, i, hi => by
    rw [koszulComplex_succ, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulComplex_isZero_X_of_lt (Fin.init x) (i + 1) (by omega),
      koszulComplex_isZero_X_of_lt (Fin.init x) i (by omega)⟩

/-- Koszul 複体の各項は有限生成自由加群である。空列では `R` 自身か零、帰納段では写像錐の項が
二つの有限自由加群の直和であること（`mappingCone_free_finite`）による。`K(x)` が台つき完全複体で
あること（`PerfectComplex/Closure.lean`）に使う。 -/
lemma koszulComplex_free_finite_X :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ),
      Module.Free R ((koszulComplex x).X i) ∧ Module.Finite R ((koszulComplex x).X i)
  | 0, x, i => by
    rw [koszulComplex_zero]
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R R)).toLinearEquiv
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
    · have h := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of R R) i hi
      exact ⟨isZero_moduleCat_free h, isZero_moduleCat_finite h⟩
  | n + 1, x, i => by
    rw [koszulComplex_succ]
    obtain ⟨h1, h2⟩ := koszulComplex_free_finite_X (Fin.init x) (i + 1)
    obtain ⟨h3, h4⟩ := koszulComplex_free_finite_X (Fin.init x) i
    exact mappingCone_free_finite _ i

/-- Koszul 複体の各項は射影的（有限自由だから）。`K(x)` を射影分解として使うとき
（`KoszulResolution.lean`）に要る。 -/
lemma koszulComplex_projective_X {n : ℕ} (x : Fin n → R) (i : ℤ) :
    Projective ((koszulComplex x).X i) :=
  projective_of_free (koszulComplex_free_finite_X x i).1

/-- Koszul 複体の正の次数のホモロジーは零（項が零だから）。 -/
lemma koszulComplex_isZero_homology_of_pos {n : ℕ} (x : Fin n → R) (i : ℤ) (hi : 0 < i) :
    IsZero ((koszulComplex x).homology i) :=
  isZero_homology_of_isZero_X _ _ (koszulComplex_isZero_X_of_pos x i hi)

/-! ## `A` 上の長さで測った Euler 標数 -/

/-- `A` 代数 `T` と `A` の元の列 `z` について、`K(z; T) = K(z; A) ⊗_A T` のホモロジーを `A` 加群として
測った Euler 標数 `χ^A(z; T) = Σ_i (-1)^i ℓ_A(H_i(z; T))`。`K(z; T)` は `z` の `T` での像の Koszul 複体
として作り、各ホモロジーを係数制限で `A` 加群とみる。無限長の項は `0` と数える（`toNat`）。

論文 (3.14) に現れる量で、`A` が正則局所環、`z` がその正則パラメータ系、`T` が `A` 上有限なら
`χ^A(z; T) = rank_A T`。この等式は `CommutativeAlgebra/RegularLocalRing.lean` の
`koszulEulerChar_eq_finrank` で、一般の有限自由分解の Euler–Poincaré 公式と
証明済みの正則局所環の性質から導き、
Lemma 3.5b の通常の長さ側（`Paper/Lemma3_5/Ordinary.lean`）で使う。 -/
noncomputable def koszulEulerChar (A T : Type u) [CommRing A] [CommRing T] [Algebra A T] {e : ℕ}
    (z : Fin e → A) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * ((Module.length A ((ModuleCat.restrictScalars
    (algebraMap A T)).obj ((koszulComplex (algebraMap A T ∘ z)).homology i))).toNat : ℝ)

end SerrePositivity

end

/-!
## Koszul 複体の基底変更

環準同型 `φ : A → C` に沿った係数拡大（`HomologicalAlgebra/BaseChange.lean` の `baseChange φ`）は
Koszul 複体と両立する：`K(z; A) ⊗_A C ≅ K(φ z; C)`（`baseChangeKoszulIso`）。Koszul 複体を写像錐の
反復で定義したので、写像錐が加法的関手と可換であること（Mathlib の
`homotopyCofiber.mapHomologicalComplexObjIso`）と、係数拡大が `a • 𝟙` を `φ(a) • 𝟙` に送ること
（`baseChange_smulId`）から、`n` についての帰納法で出る。Lemma 3.5b で `K(z; A) ⊗_A T` の Euler 評価を
計算するときと、`Tor_i^A(C, A/(z))` を Koszul ホモロジー `H_i(φ z; C)` で表すとき
（`KoszulResolution.lean` の `torAlgKoszulIso`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 基底変更と Koszul 複体の両立 `K(z; A) ⊗_A C ≅ K(φ z; C)`。`n` についての帰納法で構成する：空列では
`0` 次に置いた `A` の係数拡大が `C ⊗_A A ≅ C` であること、帰納段では、係数拡大が写像錐と可換である
こと（`mapHomologicalComplexObjIso`）、`x_n • 𝟙` が `φ(x_n) • 𝟙` に移ること（`baseChange_smulId`）、
帰納法の仮定の同型が写像錐に誘導する同型（`mapArrowIso`）を合成する。 -/
noncomputable def baseChangeKoszulIso :
    ∀ {n : ℕ} (z : Fin n → A), baseChange φ (koszulComplex z) ≅ koszulComplex (φ ∘ z)
  | 0, z =>
    (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} φ)
      (c := ComplexShape.up ℤ) 0).app (ModuleCat.of A A) ≪≫
    (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).mapIso
      (letI := φ.toAlgebra; (TensorProduct.AlgebraTensorModule.rid A C C).toModuleIso)
  | n + 1, z => by
    change baseChange φ (CochainComplex.mappingCone
      (smulId (z (Fin.last n)) (koszulComplex (Fin.init z)))) ≅
      CochainComplex.mappingCone (smulId (φ (z (Fin.last n))) (koszulComplex (Fin.init (φ ∘ z))))
    refine HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso _ _ ≪≫ ?_
    rw [baseChange_smulId]
    exact HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.isoMk (baseChangeKoszulIso (Fin.init z)) (baseChangeKoszulIso (Fin.init z))
        (by simp [smulId]))

end SerrePositivity

end
