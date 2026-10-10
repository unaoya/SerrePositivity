module

public import SerrePositivity.PerfectComplex.Closure
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# 台つき完全複体の `K₀`

論文 §3 の `K_0^J(T)`（`V(JT)` に台をもつ完全 `T` 複体の Grothendieck 群）を、生成元 `z` で
台を指定して定義する：台つき完全複体の自由アーベル群を、

- ホモトピー同値 `P ≃ P'` に対する `[P] = [P']`、
- 射 `f : P ⟶ P'`（錐も台つき完全）に対する `[Cone f] = [P'] - [P]`

で生成される部分群で割ったもの。ホモトピー圏の distinguished triangle は錐の三角と同型なので、
数学的には三角圏の `K₀` と対応する構成である。
ただし、この具体的な有限自由複体の商と、別に定義された三角圏の `K₀` との同型は本ファイルでは構成しない。

- `K0.mk P`：類 `[P]`。`K0.mk_eq_of_homotopyEquiv`、`K0.mk_cone` が関係式。
- `K0.lift χ`：関係式を保つ関数から準同型を作る。`K0.hom_ext`：準同型は類の上で決まる。
- 基本事項：同型な複体は同じ類、零複体と可縮な複体の類は `0`、シフトは符号
  `[P⟦n⟧] = (-1)^n [P]` を与える。

台つき完全複体の閉包性は `Closure.lean`、基底変更・ひねりの誘導する準同型はこのファイルの後半で定義する。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace SerrePositivity

section defs

variable (T : Type u) [CommRing T] {e : ℕ} (z : Fin e → T)

/-- `K₀` の関係式を生成する元。 -/
def K0Rels : Set (FreeAbelianGroup (PerfSupp T z)) :=
  {x | ∃ (P P' : PerfSupp T z) (_ : HomotopyEquiv P.1 P'.1),
      x = FreeAbelianGroup.of P - FreeAbelianGroup.of P'} ∪
  {x | ∃ (P P' : PerfSupp T z) (f : P.1 ⟶ P'.1)
      (hc : IsPerfectSupported z (CochainComplex.mappingCone f)),
      x = FreeAbelianGroup.of ⟨CochainComplex.mappingCone f, hc⟩ - FreeAbelianGroup.of P' +
        FreeAbelianGroup.of P}

/-- 台つき完全複体の `K₀`。 -/
abbrev K0Supported : Type (u + 1) :=
  FreeAbelianGroup (PerfSupp T z) ⧸ AddSubgroup.closure (K0Rels T z)

end defs

namespace K0

variable {T : Type u} [CommRing T] {e : ℕ} {z : Fin e → T}

/-- 類 `[P]`。 -/
def mk (P : PerfSupp T z) : K0Supported T z :=
  QuotientAddGroup.mk (FreeAbelianGroup.of P)

/-- ホモトピー同値な複体は同じ類を定める。 -/
lemma mk_eq_of_homotopyEquiv (P P' : PerfSupp T z) (h : HomotopyEquiv P.1 P'.1) :
    mk P = mk P' := by
  unfold mk
  rw [QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
  exact AddSubgroup.neg_mem _ (AddSubgroup.subset_closure (Or.inl ⟨P, P', h, rfl⟩))

/-- 錐の関係式 `[Cone f] = [P'] - [P]`。 -/
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

/-- 関係式を保つ関数から `K₀` 上の準同型を作る。 -/
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

/-- 関係式を保つ評価から作った準同型は、各複体の類で元の評価に一致する。 -/
@[simp] lemma lift_mk {β : Type*} [AddCommGroup β] (χ : PerfSupp T z → β) (hhe) (hcone)
    (P : PerfSupp T z) : lift χ hhe hcone (mk P) = χ P := by
  unfold lift mk
  exact (QuotientAddGroup.lift_mk _ _ _).trans (FreeAbelianGroup.lift_apply_of χ P)

/-- `K₀` からの準同型は類の上で決まる。 -/
lemma hom_ext {β : Type*} [AddCommGroup β] {f g : K0Supported T z →+ β}
    (h : ∀ P, f (mk P) = g (mk P)) : f = g := by
  ext P
  exact h P

/-! ## 基本事項 -/

/-- 同型な複体は同じ類。 -/
lemma mk_eq_of_iso (P P' : PerfSupp T z) (i : P.1 ≅ P'.1) : mk P = mk P' :=
  mk_eq_of_homotopyEquiv P P' (HomotopyEquiv.ofIso i)

/-- 零複体の類は `0`。 -/
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

/-- 恒等射が零ホモトピックな（可縮な）複体の類は `0`。 -/
lemma mk_eq_zero_of_homotopy_id_zero (P : PerfSupp T z) (h : Homotopy (𝟙 P.1) 0) : mk P = 0 := by
  have hZ : IsZero (0 : CochainComplex (ModuleCat.{u} T) ℤ) := isZero_zero _
  let E : HomotopyEquiv P.1 0 :=
    { hom := 0
      inv := 0
      homotopyHomInvId := (Homotopy.ofEq (by simp)).trans h.symm
      homotopyInvHomId := Homotopy.ofEq (hZ.eq_of_src _ _) }
  rw [mk_eq_of_homotopyEquiv P ⟨0, isPerfectSupported_of_isZero hZ⟩ E,
    mk_eq_zero_of_isZero _ hZ]

/-- `Cone(P → 0) ≅ P⟦1⟧`（ホモトピー圏で）。 -/
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

/-- シフト 1 は符号を変える：`[P⟦1⟧] = -[P]`。 -/
lemma mk_shift_one (P : PerfSupp T z) : mk ⟨P.1⟦(1 : ℤ)⟧, P.2.shift 1⟩ = -mk P := by
  have hZ : IsZero (0 : CochainComplex (ModuleCat.{u} T) ℤ) := isZero_zero _
  let Z : PerfSupp T z := ⟨0, isPerfectSupported_of_isZero hZ⟩
  have hc := P.2.mappingCone (0 : P.1 ⟶ 0) Z.2
  have h1 := mk_cone P Z (0 : P.1 ⟶ 0) hc
  rw [mk_eq_zero_of_isZero Z hZ, zero_sub] at h1
  rw [← h1]
  exact (mk_eq_of_homotopyEquiv _ _
    (HomotopyCategory.homotopyEquivOfIso (mappingConeToZeroIso P.1))).symm

/-- シフトは符号 `(-1)^n` を与える。 -/
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

- `K0.map φ`：基底変更 `K₀(A) → K₀(C)`（`φ : A →+* C`）。
- `K0.twistHom g`：ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`。`g • x := twistHom g⁻¹ x` で
  `G` の左作用（`K0.instDistribMulAction`、`K0.smul_mk`）。

台つき完全複体が基底変更・ひねりで保たれることは `Closure.lean`。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

namespace K0

section map

variable {A C : Type u} [CommRing A] [CommRing C] {e : ℕ} {z : Fin e → A}

/-- 基底変更の誘導する準同型 `K₀(A) → K₀(C)`。 -/
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

/-- 係数拡大が誘導する `K₀` の準同型は、複体の類を係数拡大した複体の類に送る。 -/
@[simp] lemma map_mk (φ : A →+* C) (P : PerfSupp A z) :
    map φ (mk P) = mk ⟨baseChange φ P.1, isPerfectSupported_baseChange φ P.2⟩ :=
  lift_mk _ _ _ _

end map

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T] {e : ℕ} {z : Fin e → A}

/-- ひねり `g^*` の誘導する準同型 `K₀(T) → K₀(T)`。 -/
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

/-- ひねりが誘導する `K₀` の準同型は、複体の類をひねった複体の類に送る。 -/
@[simp] lemma twistHom_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    twistHom (A := A) (z := z) g (mk P) = mk ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩ :=
  lift_mk _ _ _ _

/-- `twist 1 P ≅ P`（各項の台集合は同じ）。 -/
noncomputable def twistOneIso (P : CochainComplex (ModuleCat.{u} T) ℤ) : twist (1 : G) P ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ ModuleCat.restrictScalarsId'App (MulSemiringAction.toRingHom G T 1)
      (by ext x; simp) (P.X i))
    (fun _ _ _ ↦ by ext; rfl)

/-- `twist a (twist b P) ≅ twist (b * a) P`（各項の台集合は同じ）。 -/
noncomputable def twistMulIso (a b : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    twist a (twist b P) ≅ twist (b * a) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (ModuleCat.restrictScalarsComp'App (MulSemiringAction.toRingHom G T a)
      (MulSemiringAction.toRingHom G T b) (MulSemiringAction.toRingHom G T (b * a))
      (by ext x; simp [mul_smul]) (P.X i)).symm)
    (fun _ _ _ ↦ by ext; rfl)

/-- 群の単位元によるひねりは、台つき完全複体の `K₀` 上の恒等準同型を誘導する。 -/
lemma twistHom_one : twistHom (A := A) (T := T) (z := z) (1 : G) = AddMonoidHom.id _ :=
  hom_ext fun P ↦ by
    rw [twistHom_mk, AddMonoidHom.id_apply]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistOneIso P.1))

/-- 群の積によるひねりは、二つのひねりの逆順の合成に対応する。
係数制限の反変的な順序を明示する公式である。 -/
lemma twistHom_mul (a b : G) :
    twistHom (A := A) (T := T) (z := z) (b * a) =
      (twistHom (A := A) (z := z) a).comp (twistHom (A := A) (z := z) b) :=
  hom_ext fun P ↦ by
    rw [AddMonoidHom.comp_apply, twistHom_mk, twistHom_mk, twistHom_mk]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistMulIso a b P.1)).symm

/-- `G` の `K₀(T)` への左作用：`g • x := (g⁻¹)^* x`。 -/
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

/-- `K₀` の類への左群作用は、逆元で複体をひねった類として計算できる。 -/
lemma smul_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    g • mk P = mk ⟨twist g⁻¹ P.1, isPerfectSupported_twist z g⁻¹ P.2⟩ := by
  change twistHom (A := A) (z := z) g⁻¹ (mk P) = _
  exact twistHom_mk _ _

end twist

end K0

end SerrePositivity

end
