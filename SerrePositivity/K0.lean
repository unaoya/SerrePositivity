module

public import SerrePositivity.KoszulBaseChange
public import SerrePositivity.Perfect
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# 台つき完全複体の `K₀`

論文 §3 の `K_0^J(T)`（`V(JT)` に台をもつ完全 `T` 複体の Grothendieck 群）を、生成元 `z` で
台を指定して定義する：台つき完全複体の自由アーベル群を、

- ホモトピー同値 `P ≃ P'` に対する `[P] = [P']`、
- 射 `f : P ⟶ P'`（錐も台つき完全）に対する `[Cone f] = [P'] - [P]`

で生成される部分群で割ったもの。ホモトピー圏の distinguished triangle は錐の三角と同型なので、
これは三角圏としての `K₀` と一致する。

- `K0.mk P`：類 `[P]`。`K0.mk_eq_of_homotopyEquiv`、`K0.mk_cone` が関係式。
- `K0.lift χ`：関係式を保つ関数から準同型を作る。`K0.hom_ext`：準同型は類の上で決まる。
- `K0.map φ`：基底変更 `K₀(A) → K₀(C)`。
- `K0.twistHom g`：ひねり `g^*` の誘導する準同型。`g • x := twistHom g⁻¹ x` で `G` の左作用。

台つき完全複体が基底変更・ひねりで保たれることのうち、各項が有限自由であることの移送
（`free_baseChange` など四つ）は `sorry`（層 1、未証明）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

section defs

variable (T : Type u) [CommRing T] {e : ℕ} (z : Fin e → T)

/-- `z` に台をもつ完全 `T` 複体。 -/
abbrev PerfSupp : Type (u + 1) :=
  {P : CochainComplex (ModuleCat.{u} T) ℤ // IsPerfectSupported z P}

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

@[simp] lemma lift_mk {β : Type*} [AddCommGroup β] (χ : PerfSupp T z → β) (hhe) (hcone)
    (P : PerfSupp T z) : lift χ hhe hcone (mk P) = χ P := by
  unfold lift mk
  exact (QuotientAddGroup.lift_mk _ _ _).trans (FreeAbelianGroup.lift_apply_of χ P)

/-- `K₀` からの準同型は類の上で決まる。 -/
lemma hom_ext {β : Type*} [AddCommGroup β] {f g : K0Supported T z →+ β}
    (h : ∀ P, f (mk P) = g (mk P)) : f = g := by
  ext P
  exact h P

end K0

/-! ## 台つき完全複体の同型・基底変更・ひねりによる保存 -/

section preserve

variable {T : Type u} [CommRing T] {e : ℕ} {z : Fin e → T}

/-- 台つき完全複体は複体の同型で保たれる。 -/
lemma IsPerfectSupported.of_iso {P P' : CochainComplex (ModuleCat.{u} T) ℤ} (i : P ≅ P')
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

variable {A C : Type u} [CommRing A] [CommRing C]

/-- 台は基底変更で保たれる。 -/
lemma isSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsSupported z P) :
    IsSupported (φ ∘ z) (baseChange φ P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero, map_pow] at this
  exact ⟨this⟩

/-- 基底変更は各項の自由性を保つ（層 1、未証明）。 -/
lemma free_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Free A M] :
    Module.Free C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  sorry

/-- 基底変更は各項の有限生成性を保つ（層 1、未証明）。 -/
lemma finite_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  sorry

/-- 台つき完全複体は基底変更で保たれる。 -/
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

/-- 係数制限は `f` で固定される元によるスカラー倍と両立する。 -/
lemma restrictScalars_mapHomologicalComplex_smul_of_fixed (f : T →+* T) (c : T) (hc : f c = c)
    {ι : Type*} {cs : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} T) cs} (u : K ⟶ L) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (c • u) =
      c • ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map u := by
  ext i x
  change c • (u.f i x) = f c • (u.f i x)
  rw [hc]

variable {G : Type u} [Group G] [MulSemiringAction G T] [Algebra A T] [SMulCommClass G A T]

/-- `A` 上の作用は `A` の元の像を固定する。 -/
lemma toRingHom_algebraMap (g : G) (a : A) :
    MulSemiringAction.toRingHom G T g (algebraMap A T a) = algebraMap A T a := by
  change g • algebraMap A T a = algebraMap A T a
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

/-- `A` から来る台はひねりで保たれる。 -/
lemma isSupported_twist {e : ℕ} (z : Fin e → A) (g : G) {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : IsSupported (algebraMap A T ∘ z) P) : IsSupported (algebraMap A T ∘ z) (twist g P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have hfix : MulSemiringAction.toRingHom G T g ((algebraMap A T ∘ z) j ^ v) =
      (algebraMap A T ∘ z) j ^ v := by
    rw [map_pow, Function.comp_apply, toRingHom_algebraMap]
  have := (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomotopy H
  rw [restrictScalars_mapHomologicalComplex_smul_of_fixed _ _ hfix, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at this
  exact ⟨this⟩

/-- 環自己同型に沿った係数制限は自由性を保つ（層 1、未証明）。 -/
lemma free_twist (g : G) (M : ModuleCat.{u} T) [Module.Free T M] :
    Module.Free T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) := by
  sorry

/-- 環自己同型に沿った係数制限は有限生成性を保つ（層 1、未証明）。 -/
lemma finite_twist (g : G) (M : ModuleCat.{u} T) [Module.Finite T M] :
    Module.Finite T ((ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).obj M) := by
  sorry

/-- `A` 上の作用によるひねりは、`A` から来る台をもつ完全複体を保つ。 -/
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

end preserve

/-! ## 基底変更とひねりの `K₀` への作用 -/

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

lemma twistHom_one : twistHom (A := A) (T := T) (z := z) (1 : G) = AddMonoidHom.id _ :=
  hom_ext fun P ↦ by
    rw [twistHom_mk, AddMonoidHom.id_apply]
    exact mk_eq_of_homotopyEquiv _ _ (HomotopyEquiv.ofIso (twistOneIso P.1))

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

lemma smul_mk (g : G) (P : PerfSupp T (algebraMap A T ∘ z)) :
    g • mk P = mk ⟨twist g⁻¹ P.1, isPerfectSupported_twist z g⁻¹ P.2⟩ := by
  change twistHom (A := A) (z := z) g⁻¹ (mk P) = _
  exact twistHom_mk _ _

end twist

end K0

end SerrePositivity
