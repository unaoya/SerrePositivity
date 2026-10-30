module

public import SerrePositivity.PerfectComplex.Closure
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# 台つき完全複体の `K₀`

## 概要

論文 §3 の `K_0^J(T)`（`V(JT)` に台をもつ完全 `T` 複体の Grothendieck 群）を、台を列 `z` で指定して
`K0Supported T z` として定義する。論文では、Euler 評価 `χ`、`λ` を `K₀` 上の加法的関数として定義し
（`OrdinaryEuler.lean`、`NormalizedEuler.lean`）、`[K(z)]` が `K₀^{m}(A)` を生成すること
（`KoszulGeneration.lean`）を使って Lemma 3.5b の等式を「`K₀` 上の二つの準同型が生成元で一致する」
ことに帰着させる。このファイルはそのための `K₀` と、準同型を作る道具を与える。

## 定義

台つき完全複体 `PerfSupp T z` を生成元とする自由アーベル群を、

- ホモトピー同値 `P ≃ P'` に対する `[P] = [P']`、
- 射 `f : P ⟶ P'` に対する `[Cone f] = [P'] - [P]`

で生成される部分群 `K0Rels` で割ったもの。ホモトピー圏の完全三角形は錐の三角形と同型なので、
数学的には三角圏 `K^b(proj T)_{V(z)}` の Grothendieck 群と対応する構成である。ただし、三角圏の
`K₀` との同型は構成しない。このプロジェクトで要るのは、「関係式を保つ関数から準同型を作れる」
（`K0.lift`）と「準同型は類で決まる」（`K0.hom_ext`）の二つだけだからである。

## 規約と注意

- 錐の関係式には「錐が台つき完全」という証明 `hc` を添えている。`Closure.lean` の
  `IsPerfectSupported.mappingCone` によりこれはつねに成り立つので実質的な制限ではないが、
  関係式を証明項に依存しない形で書くために存在量化している。
- `PerfSupp T z` は複体の型なので `Type (u + 1)` に住み、`K0Supported T z` も `Type (u + 1)`。
- シフトは符号を与える：`[P⟦n⟧] = (-1)^n [P]`（`mk_shift`）。`Cone(P → 0) ≅ P⟦1⟧` と錐の関係式から
  `[P⟦1⟧] = [0] - [P] = -[P]` が出ることによる。
- 課題（K₀ のモデルの一本化）：このプロジェクトには K₀ のモデルが三つある。この `K0Supported`（自由な
  台つき完全複体）、列で台を指定した `TriangulatedK0 (SupportedPerfectHomotopy z)`、閉台の
  `K0WithSupport Z`（`ClosedSupportK0.lean`）。一本化するなら `K0WithSupport (V(z))` に寄せるのが自然だが、
  `K0Supported` は引用している定理 `Inputs.theorem_3_1_K0`（`Inputs/Descent.lean`）と Paper/Lemma3_5 の
  主張に現れるので、引用の文言を変えないよう当面は残し、`K0WithSupport` との比較の同型で結ぶ。一本化は
  引用が証明されるときに改めて行う（`formalization-plans/refactor-plan.md` §4.2.3）。

## 内容

- `K0.mk P`：類 `[P]`。`mk_eq_of_homotopyEquiv`、`mk_cone` が関係式。
- `K0.lift χ`、`K0.lift_mk`、`K0.hom_ext`。
- 基本事項：同型な複体は同じ類、零複体と可縮な複体の類は `0`、シフトの符号。
- 後半：基底変更・ひねりの誘導する準同型 `K0.map`、`K0.twistHom` と `G` の作用。

台つき完全複体の閉包性は `Closure.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace SerrePositivity

section defs

variable (T : Type u) [CommRing T] {e : ℕ} (z : Fin e → T)

/-- `K₀` の関係式を生成する元の集合。第一の集合はホモトピー同値 `P ≃ P'` に対する `[P] - [P']`、
第二の集合は射 `f : P ⟶ P'` に対する `[Cone f] - [P'] + [P]`。これらの生成する部分群で割る。 -/
def K0Rels : Set (FreeAbelianGroup (PerfSupp T z)) :=
  {x | ∃ (P P' : PerfSupp T z) (_ : HomotopyEquiv P.1 P'.1),
      x = FreeAbelianGroup.of P - FreeAbelianGroup.of P'} ∪
  {x | ∃ (P P' : PerfSupp T z) (f : P.1 ⟶ P'.1)
      (hc : IsPerfectSupported z (CochainComplex.mappingCone f)),
      x = FreeAbelianGroup.of ⟨CochainComplex.mappingCone f, hc⟩ - FreeAbelianGroup.of P' +
        FreeAbelianGroup.of P}

/-- `z` に台をもつ完全 `T` 複体の `K₀`：生成元 `PerfSupp T z` の自由アーベル群を関係式 `K0Rels` の
生成する部分群で割ったもの。論文の `K_0^{(z)}(T)`。 -/
abbrev K0Supported : Type (u + 1) :=
  FreeAbelianGroup (PerfSupp T z) ⧸ AddSubgroup.closure (K0Rels T z)

end defs

namespace K0

variable {T : Type u} [CommRing T] {e : ℕ} {z : Fin e → T}

/-- 台つき完全複体 `P` の類 `[P] ∈ K₀`。 -/
def mk (P : PerfSupp T z) : K0Supported T z :=
  QuotientAddGroup.mk (FreeAbelianGroup.of P)

/-- 第一の関係式：ホモトピー同値な複体は同じ類を定める、`[P] = [P']`。 -/
lemma mk_eq_of_homotopyEquiv (P P' : PerfSupp T z) (h : HomotopyEquiv P.1 P'.1) :
    mk P = mk P' := by
  unfold mk
  rw [QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
  exact AddSubgroup.neg_mem _ (AddSubgroup.subset_closure (Or.inl ⟨P, P', h, rfl⟩))

/-- 第二の関係式（錐の関係式）：射 `f : P ⟶ P'` に対して `[Cone f] = [P'] - [P]`。 -/
lemma mk_cone (P P' : PerfSupp T z) (f : P.1 ⟶ P'.1)
    (hc : IsPerfectSupported z (CochainComplex.mappingCone f)) :
    mk ⟨CochainComplex.mappingCone f, hc⟩ = mk P' - mk P := by
  unfold mk
  rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq]
  have : FreeAbelianGroup.of ⟨CochainComplex.mappingCone f, hc⟩ - FreeAbelianGroup.of P' +
      FreeAbelianGroup.of P ∈ AddSubgroup.closure (K0Rels T z) :=
    AddSubgroup.subset_closure (Or.inr ⟨P, P', f, hc, rfl⟩)
  have := AddSubgroup.neg_mem _ this
  convert this using 1
  abel

/-- `K₀` の普遍性：台つき完全複体の関数 `χ : PerfSupp T z → β`（`β` はアーベル群）で、ホモトピー同値で
不変（`hhe`）かつ錐の関係式 `χ(Cone f) = χ(P') - χ(P)` をみたす（`hcone`）ものは、準同型
`K₀ → β` に降りる。自由アーベル群の普遍性で `χ` を延長し、関係式の生成元が核に入ることを確かめる。
Euler 評価 `chiOrd`、`chiLam` を `K₀` 上の準同型にするのに使う。 -/
noncomputable def lift {β : Type*} [AddCommGroup β] (χ : PerfSupp T z → β)
    (hhe : ∀ (P P' : PerfSupp T z), HomotopyEquiv P.1 P'.1 → χ P = χ P')
    (hcone : ∀ (P P' : PerfSupp T z) (f : P.1 ⟶ P'.1)
      (hc : IsPerfectSupported z (CochainComplex.mappingCone f)),
      χ ⟨CochainComplex.mappingCone f, hc⟩ = χ P' - χ P) :
    K0Supported T z →+ β :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift χ) (by
    rw [AddSubgroup.closure_le]
    rintro x (⟨P, P', h, rfl⟩ | ⟨P, P', f, hc, rfl⟩)
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, hhe P P' h]
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, hcone P P' f hc])

/-- `lift χ` は類 `[P]` で `χ P` の値をとる。 -/
@[simp] lemma lift_mk {β : Type*} [AddCommGroup β] (χ : PerfSupp T z → β) (hhe) (hcone)
    (P : PerfSupp T z) : lift χ hhe hcone (mk P) = χ P := by
  unfold lift mk
  exact (QuotientAddGroup.lift_mk _ _ _).trans (FreeAbelianGroup.lift_apply_of χ P)

/-- `K₀` からの二つの準同型がすべての類 `[P]` で一致すれば等しい（`K₀` は類で生成されるから）。
Lemma 3.5b の等式を「生成元での一致」に帰着させるときに、`KoszulGeneration.lean` の
`K0.hom_ext_koszul` とあわせて使う。 -/
lemma hom_ext {β : Type*} [AddCommGroup β] {f g : K0Supported T z →+ β}
    (h : ∀ P, f (mk P) = g (mk P)) : f = g := by
  ext P
  exact h P

/-! ## 基本事項 -/

/-- 複体として同型なら同じ類（同型はホモトピー同値）。 -/
lemma mk_eq_of_iso (P P' : PerfSupp T z) (i : P.1 ≅ P'.1) : mk P = mk P' :=
  mk_eq_of_homotopyEquiv P P' (HomotopyEquiv.ofIso i)

/-- 零複体の類は `0`。零複体 `P` の恒等射の錐 `Cone(𝟙 P)` も零複体で、錐の関係式から
`[Cone(𝟙 P)] = [P] - [P] = 0`、一方 `Cone(𝟙 P) ≅ P` なので `[P] = 0`。 -/
lemma mk_eq_zero_of_isZero (P : PerfSupp T z) (hP : IsZero P.1) : mk P = 0 := by
  have hc : IsZero (CochainComplex.mappingCone (𝟙 P.1)) := by
    refine isZero_of_isZero_X fun i ↦ ?_
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨(HomologicalComplex.eval _ _ _).map_isZero hP,
      (HomologicalComplex.eval _ _ _).map_isZero hP⟩
  have h1 := mk_cone P P (𝟙 P.1) (isPerfectSupported_of_isZero hc)
  have h2 := mk_eq_of_iso ⟨_, isPerfectSupported_of_isZero hc⟩ P (hc.iso hP)
  rw [sub_self] at h1
  rw [← h2, h1]

/-- ホモトピー圏での同型 `Cone(P → 0) ≅ P⟦1⟧`。完全三角形 `P → 0 → Cone(P → 0) → P⟦1⟧` と、
可縮な三角形 `P → 0 → P⟦1⟧ → P⟦1⟧` は最初の二つの頂点が一致するので、三角圏の公理により
三番目の頂点も同型になる（Mathlib の `isoTriangleOfIso₁₂`）。 -/
noncomputable def mappingConeToZeroIso (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    (homotopyQuot T).obj (CochainComplex.mappingCone (0 : P ⟶ 0)) ≅
      (homotopyQuot T).obj (P⟦(1 : ℤ)⟧) := by
  have hZ : IsZero ((homotopyQuot T).obj (0 : CochainComplex (ModuleCat.{u} T) ℤ)) :=
    Functor.map_isZero _ (isZero_zero _)
  let T₂ := Triangle.mk (0 : (homotopyQuot T).obj P ⟶ 0) 0 (𝟙 (((homotopyQuot T).obj P)⟦(1 : ℤ)⟧))
  let e := isoTriangleOfIso₁₂ (CochainComplex.mappingCone.triangleh (0 : P ⟶ 0)) T₂
    (HomotopyCategory.mappingCone_triangleh_distinguished _) (contractible_distinguished₂ _)
    (Iso.refl _) (hZ.iso (isZero_zero _)) ((isZero_zero _).eq_of_tgt _ _)
  exact Triangle.π₃.mapIso e ≪≫ (((homotopyQuot T).commShiftIso (1 : ℤ)).app P).symm

/-- シフト `1` は符号を変える：`[P⟦1⟧] = -[P]`。錐の関係式を `P → 0` に適用すると
`[Cone(P → 0)] = [0] - [P] = -[P]`、そして `Cone(P → 0) ≃ P⟦1⟧`（`mappingConeToZeroIso`）。 -/
lemma mk_shift_one (P : PerfSupp T z) : mk ⟨P.1⟦(1 : ℤ)⟧, P.2.shift 1⟩ = -mk P := by
  have hZ : IsZero (0 : CochainComplex (ModuleCat.{u} T) ℤ) := isZero_zero _
  let Z : PerfSupp T z := ⟨0, isPerfectSupported_of_isZero hZ⟩
  have hc := P.2.mappingCone (0 : P.1 ⟶ 0) Z.2
  have h1 := mk_cone P Z (0 : P.1 ⟶ 0) hc
  rw [mk_eq_zero_of_isZero Z hZ, zero_sub] at h1
  rw [← h1]
  exact (mk_eq_of_homotopyEquiv _ _
    (HomotopyCategory.homotopyEquivOfIso (mappingConeToZeroIso P.1))).symm

/-- シフト `n` は符号 `(-1)^n` を与える：`[P⟦n⟧] = (-1)^n [P]`。`n` についての（正負両方向の）
帰納法で、`P⟦n + 1⟧ ≅ (P⟦n⟧)⟦1⟧`（`shiftFunctorAdd'`）と `mk_shift_one` による。
デヴィサージュ（`KoszulGeneration.lean`）で最上段を `0` 次にそろえるときに使う。 -/
lemma mk_shift (P : PerfSupp T z) (n : ℤ) :
    mk ⟨P.1⟦n⟧, P.2.shift n⟩ = ((n.negOnePow : ℤˣ) : ℤ) • mk P := by
  induction n using Int.induction_on with
  | zero =>
    rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact mk_eq_of_iso _ _ ((shiftFunctorZero _ ℤ).app P.1)
  | succ n ih =>
    have h := mk_eq_of_iso ⟨P.1⟦(n + 1 : ℤ)⟧, P.2.shift _⟩
      ⟨(P.1⟦(n : ℤ)⟧)⟦(1 : ℤ)⟧, (P.2.shift _).shift 1⟩
      ((shiftFunctorAdd' _ (n : ℤ) 1 (n + 1) rfl).app P.1)
    rw [h, mk_shift_one ⟨P.1⟦(n : ℤ)⟧, P.2.shift _⟩, ih, Int.negOnePow_succ, Units.val_neg,
      neg_smul]
  | pred n ih =>
    have h := mk_eq_of_iso ⟨P.1⟦(-n : ℤ)⟧, P.2.shift _⟩
      ⟨(P.1⟦(-n - 1 : ℤ)⟧)⟦(1 : ℤ)⟧, (P.2.shift _).shift 1⟩
      ((shiftFunctorAdd' _ (-n - 1 : ℤ) 1 (-n) (by omega)).app P.1)
    rw [mk_shift_one ⟨P.1⟦(-n - 1 : ℤ)⟧, P.2.shift _⟩, ih] at h
    rw [← neg_neg (mk ⟨P.1⟦(-n - 1 : ℤ)⟧, _⟩), ← h, Int.negOnePow_sub, Int.negOnePow_one,
      mul_neg, mul_one, Units.val_neg, neg_smul]

end K0

end SerrePositivity

end

/-!
## 基底変更とひねりの `K₀` への作用

- `K0.map φ`：基底変更の誘導する準同型 `K₀(A) → K₀(C)`（`φ : A →+* C`）、`[P] ↦ [P ⊗_A C]`。
  論文 (3.6) の `K_0^{m}(A) → K_0^{m}(T)`。
- `K0.twistHom g`：ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`、`[P] ↦ [g^*P]`。ひねりは係数制限
  なので反変で、`(b a)^* = a^* ∘ b^*`（`twistHom_mul`）。左作用にするには逆元をとって
  `g • x := twistHom g⁻¹ x` とする（`K0.instDistribMulAction`、`K0.smul_mk`）。論文 §5.1 の `G` の
  `K_0^{m}(T)` への作用。

どちらも `K0.lift` で作る。関手がホモトピー同値を保ち（`mapHomotopyEquiv`）、写像錐と可換である
（Mathlib の `homotopyCofiber.mapHomologicalComplexObjIso`）ので、関係式を保つ。台つき完全複体が
基底変更・ひねりで保たれることは `Closure.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

namespace K0

section map

variable {A C : Type u} [CommRing A] [CommRing C] {e : ℕ} {z : Fin e → A}

/-- 基底変更 `φ : A →+* C` の誘導する準同型 `K₀(A)_{(z)} → K₀(C)_{(φ z)}`、`[P] ↦ [P ⊗_A C]`。
`K0.lift` で作る：係数拡大関手はホモトピー同値を保ち、`(Cone f) ⊗_A C ≅ Cone(f ⊗_A C)` なので
錐の関係式も保つ。 -/
noncomputable def map (φ : A →+* C) : K0Supported A z →+ K0Supported C (φ ∘ z) :=
  lift (fun P ↦ mk ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩)
    (fun P P' h ↦ mk_eq_of_homotopyEquiv _ _
      ((ModuleCat.extendScalars.{u, u, u} φ).mapHomotopyEquiv h))
    (fun P P' f hc ↦ by
      have i : baseChange φ (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone
            (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map f) :=
        HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f _
      have hc' := (isPerfectSupported_baseChange φ hc).of_iso i
      rw [mk_eq_of_homotopyEquiv ⟨_, isPerfectSupported_baseChange φ hc⟩ ⟨_, hc'⟩
        (HomotopyEquiv.ofIso i)]
      exact mk_cone ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩
        ⟨baseChange φ P'.1, isPerfectSupported_baseChange φ P'.2⟩ _ hc')

/-- `map φ [P] = [P ⊗_A C]`。 -/
@[simp] lemma map_mk (φ : A →+* C) (P : PerfSupp A z) :
    map φ (mk P) = mk ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩ :=
  lift_mk _ _ _ _

end map

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T] {e : ℕ} {z : Fin e → A}

/-- ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`、`[P] ↦ [g^*P]`。台は `A` の元の列 `z` から来るもの
に限る（`isPerfectSupported_twist`）。`K0.lift` で作る：係数制限関手はホモトピー同値を保ち、
写像錐と可換なので関係式を保つ。 -/
noncomputable def twistHom (g : G) :
    K0Supported T (algebraMap A T ∘ z) →+ K0Supported T (algebraMap A T ∘ z) :=
  lift (fun P ↦ mk ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩)
    (fun P P' h ↦ mk_eq_of_homotopyEquiv _ _
      ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomotopyEquiv h))
    (fun P P' f hc ↦ by
      have i : twist g (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone
            (((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomologicalComplex
              _).map f) :=
        HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f _
      have hc' := (isPerfectSupported_twist z g hc).of_iso i
      rw [mk_eq_of_homotopyEquiv ⟨_, isPerfectSupported_twist z g hc⟩ ⟨_, hc'⟩
        (HomotopyEquiv.ofIso i)]
      exact mk_cone ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩
        ⟨twist g P'.1, isPerfectSupported_twist z g P'.2⟩ _ hc')

/-- `twistHom g [P] = [g^*P]`。 -/
@[simp] lemma twistHom_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    twistHom (A := A) (z := z) g (mk P) = mk ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩ :=
  lift_mk _ _ _ _

/-- 単位元によるひねりは何もしない：`1^*P ≅ P`。各項の台集合は同じで、作用は恒等な環準同型に沿った
係数制限なので、恒等写像が複体の同型を与える。 -/
noncomputable def twistOneIso (P : CochainComplex (ModuleCat.{u} T) ℤ) : twist (1 : G) P ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ ModuleCat.restrictScalarsId'App (MulSemiringAction.toRingHom G T 1)
      (by ext x; simp) (P.X i))
    (fun _ _ _ ↦ by ext; rfl)

/-- ひねりの合成：`a^*(b^*P) ≅ (b a)^*P`。`b^*P` の作用は `t • x = (b • t) • x`、それをさらに `a` で
ひねると `t • x = (b • (a • t)) • x = ((b a) • t) • x` となるから。順序が逆になるのは係数制限が
反変だからである。 -/
noncomputable def twistMulIso (a b : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    twist a (twist b P) ≅ twist (b * a) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (ModuleCat.restrictScalarsComp'App (MulSemiringAction.toRingHom G T a)
      (MulSemiringAction.toRingHom G T b) (MulSemiringAction.toRingHom G T (b * a))
      (by ext x; simp [mul_smul]) (P.X i)).symm)
    (fun _ _ _ ↦ by ext; rfl)

/-- `twistHom 1 = id`（`twistOneIso` と `hom_ext`）。 -/
lemma twistHom_one : twistHom (A := A) (T := T) (z := z) (1 : G) = AddMonoidHom.id _ :=
  hom_ext fun P ↦ by
    rw [twistHom_mk, AddMonoidHom.id_apply]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistOneIso P.1))

/-- `twistHom (b * a) = twistHom a ∘ twistHom b`（`twistMulIso` と `hom_ext`）。ひねりは反変なので
順序が逆になる。 -/
lemma twistHom_mul (a b : G) :
    twistHom (A := A) (T := T) (z := z) (b * a) =
      (twistHom (A := A) (z := z) a).comp (twistHom (A := A) (z := z) b) :=
  hom_ext fun P ↦ by
    rw [AddMonoidHom.comp_apply, twistHom_mk, twistHom_mk, twistHom_mk]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistMulIso a b P.1)).symm

/-- `G` の `K₀(T)` への左作用 `g • x := twistHom g⁻¹ x = (g⁻¹)^* x`。`twistHom` が反変なので逆元で
ひねると共変になる：`(g h) • x = twistHom (h⁻¹ g⁻¹) x = twistHom g⁻¹ (twistHom h⁻¹ x) = g • (h • x)`
（`twistHom_mul`）。加法群の準同型なので `DistribMulAction`。論文 §5.1 の作用で、`G` 不変な元
（`Σ_g g • [P]`）を考えるときに使う（`Paper/Section5/`）。 -/
noncomputable instance instDistribMulAction :
    DistribMulAction G (K0Supported T (algebraMap A T ∘ z)) where
  smul g := twistHom (A := A) (z := z) g⁻¹
  one_smul x := by
    change twistHom (A := A) (z := z) (1 : G)⁻¹ x = x
    rw [inv_one, twistHom_one, AddMonoidHom.id_apply]
  mul_smul g h x := by
    change twistHom (A := A) (z := z) (g * h)⁻¹ x =
      twistHom (A := A) (z := z) g⁻¹ (twistHom (A := A) (z := z) h⁻¹ x)
    rw [mul_inv_rev, twistHom_mul, AddMonoidHom.comp_apply]
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

/-- `g • [P] = [(g⁻¹)^* P]`。 -/
lemma smul_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    g • mk P = mk ⟨twist g⁻¹ P.1, isPerfectSupported_twist z g⁻¹ P.2⟩ := by
  change twistHom (A := A) (z := z) g⁻¹ (mk P) = _
  exact twistHom_mk _ _

end twist

end K0

end SerrePositivity

end
