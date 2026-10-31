module

public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.FiniteFreeBaseChange
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-! # 台つき完全複体とその K₀

## 概要

台つき完全複体の性質 `IsPerfectSupported z P`（有界・各項が有限自由・z に台を持つ）が、同型・写像錐・シフト・零複体・基底変更・ひねりで保たれることを示し、論文 §3 の K_0^J(T) を `K0Supported T z` として定義する。

## 方針

K₀ は生成元と、写像錐の三角形による関係式で定める。

## 規約

`K0Supported` は Inputs/Descent の引用 `theorem_3_1_K0` の型に現れるので名前と形を変えない。K₀ のモデルの一本化は保留（refactor-plan §4.2.3）。

## 使われ方

`Free/Euler`、Inputs/Descent、Paper の Lemma 3.5。
-/

@[expose] public noncomputable section

universe u

section ClosurePart

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R] {e : ℕ} {z : Fin e → R}

/-! ## 同型・写像錐・シフト・零複体 -/

/-- 複体の同型 `i : P ≅ P'` で台つき完全複体の条件は移る。各項の同型で有界性・有限自由性を移し、
台の条件は零ホモトピーを `i⁻¹ ≫ - ≫ i` で共役する。 -/
lemma IsPerfectSupported.of_iso {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (i : P ≅ P')
    (h : IsPerfectSupported z P) : IsPerfectSupported z P' where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (HomologicalComplex.Hom.isoApp i n).isZero_iff.mp (hab n hn)⟩
  free n := by
    have := h.free n
    exact Module.Free.of_equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  finite n := by
    have := h.finite n
    exact Module.Finite.equiv (HomologicalComplex.Hom.isoApp i n).toLinearEquiv
  supported := by
    obtain ⟨v, hv⟩ := h.supported
    refine ⟨v, fun j ↦ ?_⟩
    obtain ⟨H⟩ := hv j
    refine ⟨(Homotopy.ofEq ?_).trans (((H.compRight i.hom).compLeft i.inv).trans
      (Homotopy.ofEq ?_))⟩
    · rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
    · simp

/-- 台つき完全複体の間の射 `f : X ⟶ Y` の写像錐は台つき完全複体。錐の項は `Cone^i = X^{i+1} ⊕ Y^i`
なので、`X` が `[a, b]`、`Y` が `[c, d]` に乗れば錐は `[min(a-1, c), max(b, d)]` に乗り、各項は
有限自由加群の直和で有限自由（`mappingCone_free_finite`）。台の条件は `IsSupported.mappingCone`。
`K₀` の錐の関係式（`K0.lean`）に現れる錐が `PerfSupp` の元であることの根拠。 -/
lemma IsPerfectSupported.mappingCone {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y)
    (hX : IsPerfectSupported z X) (hY : IsPerfectSupported z Y) :
    IsPerfectSupported z (CochainComplex.mappingCone f) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hX.bounded
    obtain ⟨c, d, hcd⟩ := hY.bounded
    refine ⟨min (a - 1) c, max b d, fun i hi ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · apply hab
      rcases hi with hi | hi
      · left; omega
      · right; omega
    · apply hcd
      rcases hi with hi | hi
      · left; omega
      · right; omega
  free i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).1
  finite i := by
    have := hX.free (i + 1); have := hY.free i
    have := hX.finite (i + 1); have := hY.finite i
    exact (mappingCone_free_finite f i).2
  supported := hX.supported.mappingCone f hY.supported

/-- 台つき完全複体のシフト `P⟦n⟧`（`(P⟦n⟧)^i = P^{i+n}`）は台つき完全複体。 -/
lemma IsPerfectSupported.shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsPerfectSupported z P) (n : ℤ) : IsPerfectSupported z (P⟦n⟧) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hP.bounded
    exact ⟨a - n, b - n, fun i hi ↦ hab (i + n) (by omega)⟩
  free i := hP.free (i + n)
  finite i := hP.finite (i + n)
  supported := hP.supported.shift n

/-- 零複体は（どんな `z` についても）台つき完全複体。各項が零なので有界・有限自由は自明で、
台の条件は `v = 0` でよい（零複体上の射はすべて零）。 -/
lemma isPerfectSupported_of_isZero {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsZero P) :
    IsPerfectSupported z P where
  bounded := ⟨0, 0, fun i _ ↦ (HomologicalComplex.eval _ _ i).map_isZero hP⟩
  free i := isZero_moduleCat_free ((HomologicalComplex.eval _ _ i).map_isZero hP)
  finite i := isZero_moduleCat_finite ((HomologicalComplex.eval _ _ i).map_isZero hP)
  supported := ⟨0, fun _ ↦ ⟨Homotopy.ofEq (hP.eq_of_src _ _)⟩⟩

/-! ## 基底変更 -/

section baseChange

variable {A C : Type u} [CommRing A] [CommRing C]

/-- `z` に台をもつ完全 `A` 複体 `P` の基底変更 `P ⊗_A C` は、`φ ∘ z` に台をもつ完全 `C` 複体。
係数拡大は零加群を零加群に送り（有界性）、有限自由加群を有限自由加群に送り、台の条件を保つ
（`isSupported_baseChange`）。論文 (3.6) の `K_0^{m}(A) → K_0^{m}(T)` を定義する根拠。 -/
lemma isPerfectSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsPerfectSupported z P) :
    IsPerfectSupported (φ ∘ z) (baseChange φ P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦ (ModuleCat.extendScalars.{u, u, u} φ).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_baseChange φ (P.X n)
  finite n := by
    have := h.finite n
    exact finite_baseChange φ (P.X n)
  supported := isSupported_baseChange φ h.supported

end baseChange

/-! ## ひねり -/

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- `g⁻¹` の `T` への作用を環同型 `T ≃+* T` とみたもの。`twist g P` の各項への恒等写像が、この
環同型に沿った半線形写像になる（`twistSemilinearEquiv`）。 -/
noncomputable abbrev twistInvEquiv (g : G) : T ≃+* T := MulSemiringAction.toRingEquiv G T g⁻¹

/-- Mathlib の半線形同値 `M ≃ₛₗ[σ] N` は、`σ` とその逆が互いに逆であることを
`RingHomInvPair` インスタンスで要求する。`twistInvEquiv g` とその逆について登録しておく。 -/
instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).toRingHom
    (twistInvEquiv (T := T) g).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (twistInvEquiv (T := T) g)

/-- 上のインスタンスの逆向き。 -/
instance (g : G) : RingHomInvPair (twistInvEquiv (T := T) g).symm.toRingHom
    (twistInvEquiv (T := T) g).toRingHom :=
  RingHomInvPair.symm _ _

/-- ひねり `g^*M`（`restrictScalars (g •)` した `M`。台集合は同じで、作用は `t •' x = (g • t) • x`）
への恒等写像 `x ↦ x` は、環同型 `g⁻¹ • : T ≃+* T` に沿った半線形同型である：
`t •' x = (g • (g⁻¹ • t)) •' x`、すなわち `φ(t • x) = (g⁻¹ • t) •' φ(x)`。半線形同型で自由性・
有限生成性が移るので、ひねりがこれらを保つことが従う。 -/
noncomputable def twistSemilinearEquiv (g : G) (M : ModuleCat.{u} T) :
    M ≃ₛₗ[(twistInvEquiv (T := T) g).toRingHom]
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' t x := by
    change t • x = (g • (g⁻¹ • t)) • x
    rw [smul_inv_smul]
  left_inv _ := rfl
  right_inv _ := rfl

/-- ひねり `g^*M` は、`M` が自由なら自由（`twistSemilinearEquiv` と、半線形同型で自由性が移ること）。 -/
lemma free_twist (g : G) (M : ModuleCat.{u} T) [Module.Free T M] :
    Module.Free T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Free.of_equiv (twistSemilinearEquiv g M)

/-- ひねり `g^*M` は、`M` が有限生成なら有限生成（半線形全射の像だから）。 -/
lemma finite_twist (g : G) (M : ModuleCat.{u} T) [Module.Finite T M] :
    Module.Finite T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) :=
  Module.Finite.of_surjective (twistSemilinearEquiv g M).toLinearMap
    (twistSemilinearEquiv g M).surjective

/-- `G` が `T` に `A` 線形に作用するとき、`A` の元の列 `z` から来る台をもつ完全 `T` 複体 `P` の
ひねり `g^*P` は、同じ `z` に台をもつ完全複体。項は台集合が同じなので有界性はそのまま、有限自由性は
`free_twist`・`finite_twist`、台の条件は `isSupported_twist`。§5.1 の `G` の `K₀^{m}(T)` への作用
（`K0.lean` の `twistHom`）の根拠。 -/
lemma isPerfectSupported_twist {e : ℕ} (z : Fin e → A) (g : G)
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (h : IsPerfectSupported (algebraMap A T ∘ z) P) :
    IsPerfectSupported (algebraMap A T ∘ z) (twist g P) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, fun n hn ↦
      (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).map_isZero (hab n hn)⟩
  free n := by
    have := h.free n
    exact free_twist g (P.X n)
  finite n := by
    have := h.finite n
    exact finite_twist g (P.X n)
  supported := isSupported_twist z g h.supported

end twist

/-! ## Koszul 複体は台つき完全複体 -/

/-- Koszul 複体 `K(x)` は `x` に台をもつ完全複体：`[-n, 0]` に乗り、各項は有限自由
（`CommutativeAlgebra/Koszul.lean`）、`x` に台をもつ（`isSupported_koszulComplex`）。 -/
theorem isPerfectSupported_koszulComplex {n : ℕ} (x : Fin n → R) :
    IsPerfectSupported x (koszulComplex x) where
  bounded := ⟨-(n : ℤ), 0, fun i hi ↦ by
    rcases hi with hi | hi
    · exact koszulComplex_isZero_X_of_lt x i hi
    · exact koszulComplex_isZero_X_of_pos x i hi⟩
  free i := (koszulComplex_free_finite_X x i).1
  finite i := (koszulComplex_free_finite_X x i).2
  supported := isSupported_koszulComplex x

/-- Koszul 複体を `PerfSupp R x`（`x` に台をもつ完全複体の型）の元として包んだもの。その類
`K0.mk (koszulPerfSupp x)` が `K₀^{(x)}` を生成する（`KoszulGeneration.lean`）。 -/
noncomputable def koszulPerfSupp {n : ℕ} (x : Fin n → R) : PerfSupp R x :=
  ⟨koszulComplex x, isPerfectSupported_koszulComplex x⟩

end SerrePositivity

end ClosurePart

section K0Part

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


end K0Part
