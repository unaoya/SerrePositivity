module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Logic.Function.Iterate

/-!
# δ 安定イデアル・商・δ 閉包（BS 著者版 Lemma 2.9、BS 著者版 Example 2.10）

## 概要
δ 安定イデアルによる商の δ 構造と普遍性、δ 閉包（I を含む最小の δ 安定イデアル）とその生成元表示。
BS 著者版 Lemma 2.9・Example 2.10。

## 方針
切断 A → W₂(A) → W₂(A/I) が I を零に送ることから商へ降ろす。生成元の表示は、生成元の δ が入れば
イデアル全体が δ 安定であること（加法公式の補正項と積公式の各項）から。

## 規約
p ねじれを許す。

## 使われ方
相対自由 δ 環の表示（Free/RelativeFreeDelta）、d で割る包（Division）。
-/

@[expose] public noncomputable section
universe u v

/-! ## δ安定イデアルの閉包

BS 著者版 Example 2.10のδ安定化を、元のイデアルを含むδ安定イデアルの
交わりとして構成する。商環のδ構造の構成とは独立な、最小性の部分を証明する。
-/

section DeltaIdeal

namespace SerrePositivity.BhattScholze.DeltaStructure

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δ安定イデアルの逆像はδ安定。δ射の可換性を使い、商の普遍性に備える。 -/
theorem IsDeltaHom.isStable_comap {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) {J : Ideal B} (hJ : E.IsStable J) :
    D.IsStable (J.comap f) := by
  intro x hx
  change f (D.delta x) ∈ J
  rw [hf x]
  exact hJ (f x) hx

/-- δ閉包：Iを含むすべてのδ安定イデアルの交わり（BS 著者版 Example 2.10 のδ 安定化の構成）。
余分な正則性・完備性を要求せず、δ環の商構成に用いる。 -/
def deltaClosure (D : DeltaStructure p A) (I : Ideal A) : Ideal A :=
  sInf {J : Ideal A | I ≤ J ∧ D.IsStable J}

/-- 元がδ閉包に属するのは、Iを含むすべてのδ安定イデアルに属するとき。 -/
theorem mem_deltaClosure (D : DeltaStructure p A) (I : Ideal A) (x : A) :
    x ∈ D.deltaClosure I ↔ ∀ J : Ideal A, I ≤ J → D.IsStable J → x ∈ J := by
  simp [deltaClosure, Submodule.mem_sInf]

/-- 元のイデアルはそのδ閉包に含まれる。 -/
theorem le_deltaClosure (D : DeltaStructure p A) (I : Ideal A) : I ≤ D.deltaClosure I := by
  intro x hx
  rw [mem_deltaClosure]
  exact fun J hIJ _ ↦ hIJ hx

/-- δ閉包はδで安定。交わりを取る各イデアルのδ安定性を使う。 -/
theorem isStable_deltaClosure (D : DeltaStructure p A) (I : Ideal A) :
    D.IsStable (D.deltaClosure I) := by
  intro x hx
  rw [mem_deltaClosure] at hx ⊢
  intro J hIJ hJ
  exact hJ x (hx J hIJ hJ)

/-- δ閉包はIを含むδ安定イデアルの中で最小。商を経由する射の構成に使う。 -/
theorem deltaClosure_le (D : DeltaStructure p A) {I J : Ideal A}
    (hIJ : I ≤ J) (hJ : D.IsStable J) : D.deltaClosure I ≤ J := by
  intro x hx
  exact (D.mem_deltaClosure I x).mp hx J hIJ hJ

/-- δで安定なイデアルのδ閉包は元のイデアル。 -/
theorem deltaClosure_eq (D : DeltaStructure p A) {I : Ideal A} (hI : D.IsStable I) :
    D.deltaClosure I = I :=
  le_antisymm (D.deltaClosure_le le_rfl hI) (D.le_deltaClosure I)

/-- δ閉包はイデアルの包含に関して単調。 -/
theorem deltaClosure_mono (D : DeltaStructure p A) {I J : Ideal A} (hIJ : I ≤ J) :
    D.deltaClosure I ≤ D.deltaClosure J :=
  D.deltaClosure_le (hIJ.trans (D.le_deltaClosure J)) (D.isStable_deltaClosure J)

/-- δ閉包を二度取っても変わらない。 -/
@[simp] theorem deltaClosure_idempotent (D : DeltaStructure p A) (I : Ideal A) :
    D.deltaClosure (D.deltaClosure I) = D.deltaClosure I :=
  D.deltaClosure_eq (D.isStable_deltaClosure I)

/-- δ射がIを零に送れば、そのδ閉包も零に送る。
核のδ安定性と最小性により、δ安定商の普遍性の核条件を得る。 -/
theorem IsDeltaHom.deltaClosure_le_ker {B : Type v} [CommRing B]
    {D : DeltaStructure p A} {E : DeltaStructure p B} {f : A →+* B}
    (hf : D.IsDeltaHom E f) {I : Ideal A} (hI : I ≤ RingHom.ker f) :
    D.deltaClosure I ≤ RingHom.ker f :=
  D.deltaClosure_le hI hf.isStable_ker

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaIdeal

/-! ## δ安定イデアルによる商δ環

BS 著者版 Lemma 2.9とBS 著者版 Example 2.10。W₂切断を商へ降下し、
pねじれの有無によらない商δ構造とδ射としての普遍性を構成する。
-/

section DeltaQuotient

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

namespace DeltaStructure

/-- δ安定イデアル上では、切断を商のW₂に送った像が零になる。
第0座標は元のイデアル、第1座標はδ安定性を使う。 -/
theorem sectionHom_quotient_eq_zero (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (x : A) (hx : x ∈ I) :
    ((wittTwoMap (p := p) (Ideal.Quotient.mk I)).comp D.sectionHom) x = 0 := by
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff,
      TruncatedWittVector.coeff_zero]
    change Ideal.Quotient.mk I ((D.sectionHom x).coeff 0) = 0
    rw [D.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · simp only [RingHom.comp_apply, wittTwoMap_coeff, TruncatedWittVector.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI x hx)

/-- δ安定イデアルによる商δ構造（BS 著者版 Lemma 2.9 の存在方向の構成）。
  切断の環準同型を商の普遍性で降下する。 -/
def quotient (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I) :
    DeltaStructure p (A ⧸ I) where
  sectionHom := Ideal.Quotient.lift I
    ((wittTwoMap (p := p) (Ideal.Quotient.mk I)).comp D.sectionHom)
    (D.sectionHom_quotient_eq_zero I hI)
  coeff_zero := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.Quotient.lift_mk, D.coeff_zero]

/-- 商のδは元環のδを標準写像で送ったもの。 -/
@[simp] theorem quotient_delta_mk (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (x : A) :
    (D.quotient I hI).delta (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (D.delta x) := by
  simp [quotient, delta, Ideal.Quotient.lift_mk]

/-- δ安定商への標準写像はδ射である（BS 著者版 Lemma 2.9の存在）。 -/
theorem isDeltaHom_quotient_mk (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I) :
    D.IsDeltaHom (D.quotient I hI) (Ideal.Quotient.mk I) := by
  intro x
  exact (D.quotient_delta_mk I hI x).symm

/-- 標準写像と両立する商δ構造は一意。全射性から各元のδを比較する。 -/
theorem quotient_unique (D : DeltaStructure p A) (I : Ideal A) (hI : D.IsStable I)
    (E : DeltaStructure p (A ⧸ I)) (hE : D.IsDeltaHom E (Ideal.Quotient.mk I)) :
    E = D.quotient I hI := by
  apply ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotient_delta_mk, ← hE a]

/-- 商に標準写像と両立するδ構造があるのは、イデアルがδ安定である場合に限る（BS 著者版 Lemma 2.9）。
存在・一意性をp正則性なしにまとめる。 -/
theorem isStable_iff_existsUnique_quotient (D : DeltaStructure p A) (I : Ideal A) :
    D.IsStable I ↔ ∃! E : DeltaStructure p (A ⧸ I), D.IsDeltaHom E (Ideal.Quotient.mk I) := by
  constructor
  · intro hI
    exact ⟨D.quotient I hI, D.isDeltaHom_quotient_mk I hI,
      fun E hE ↦ D.quotient_unique I hI E hE⟩
  · rintro ⟨E, hE, _⟩
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hE x, Ideal.Quotient.eq_zero_iff_mem.mpr hx, delta_zero]

/-- Iを零に送るδ射は、δ安定商からの一意なδ射に降下する（BS 著者版 Lemma 2.9 の商からの射の形）。
環準同型の商の普遍性とδの標準像上の公式を使う。 -/
theorem existsUnique_quotient_lift (D : DeltaStructure p A) (I : Ideal A)
    (hI : D.IsStable I) (E : DeltaStructure p B) (f : A →+* B)
    (hf : D.IsDeltaHom E f) (hker : I ≤ RingHom.ker f) :
    ∃! g : (A ⧸ I) →+* B,
      g.comp (Ideal.Quotient.mk I) = f ∧ (D.quotient I hI).IsDeltaHom E g := by
  let g := Ideal.Quotient.lift I f (fun x hx ↦ hker hx)
  have hg : g.comp (Ideal.Quotient.mk I) = f := by
    ext x
    rfl
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotient_delta_mk]
    change f (D.delta a) = E.delta (f a)
    exact hf a
  · intro k hk
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun hk.1 a).trans (DFunLike.congr_fun hg a).symm

/-- δ閉包で割った商は、Iを零に送るδ射の普遍対象（BS 著者版 Example 2.10 の普遍性の部分）。
Iそのもののδ安定性は要求しない。 -/
theorem existsUnique_deltaClosure_quotient_lift (D : DeltaStructure p A) (I : Ideal A)
    (E : DeltaStructure p B) (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hker : I ≤ RingHom.ker f) :
    ∃! g : (A ⧸ D.deltaClosure I) →+* B,
      g.comp (Ideal.Quotient.mk (D.deltaClosure I)) = f ∧
        (D.quotient (D.deltaClosure I) (D.isStable_deltaClosure I)).IsDeltaHom E g :=
  D.existsUnique_quotient_lift (D.deltaClosure I) (D.isStable_deltaClosure I)
    E f hf (hf.deltaClosure_le_ker hker)

end DeltaStructure
end SerrePositivity.BhattScholze

end DeltaQuotient

/-! ## 反復δ像によるδ閉包の生成

BS 著者版 Example 2.10の表示を、δ安定イデアルの最小性と比較する。
生成元でのδ安定性をイデアル全体へ拡張する際にδの加法・積公式を用いる。
-/

section DeltaClosureGeneration

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- x,yがイデアルIに属すれば、δ加法の繰上り項もIに属する。
商へのWitt写像で両Teichmüller元を零へ送る。 -/
theorem additionCarry_mem (I : Ideal A) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hx0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hy0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  simp only [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, hx0, hy0,
    WittVector.teichmuller_zero, add_zero, WittVector.zero_coeff]

/-- 生成元のδが生成イデアルに属すれば、そのイデアルはδ安定。
加法の繰上り項と積公式の各項がイデアルに属することを生成帰納法で示す。 -/
theorem isStable_span (D : DeltaStructure p A) (s : Set A)
    (hs : ∀ x ∈ s, D.delta x ∈ Ideal.span s) : D.IsStable (Ideal.span s) := by
  intro x hx
  change x ∈ Submodule.span A s at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [D.delta_add]
      exact (Ideal.span s).add_mem ((Ideal.span s).add_mem ihx ihy)
        (additionCarry_mem (Ideal.span s) hx hy)
  | smul r x hx ih =>
      change D.delta (r * x) ∈ Ideal.span s
      rw [D.delta_mul]
      exact (Ideal.span s).add_mem
        ((Ideal.span s).add_mem ((Ideal.span s).mul_mem_left (r ^ p) ih)
          ((Ideal.span s).mul_mem_left (D.delta r)
            ((Ideal.span s).pow_mem_of_mem hx p (Fact.out : p.Prime).pos)))
        ((Ideal.span s).mul_mem_left ((p : A) * D.delta r) ih)

/-- 生成イデアルのδ閉包は、指定生成元だけの全反復δ像で生成される。 -/
theorem deltaClosure_span_eq_span_generator_iterates
    (D : DeltaStructure p A) (s : Set A) :
    D.deltaClosure (Ideal.span s) = Ideal.span (⋃ n : ℕ, D.delta^[n] '' s) := by
  let t : Set A := ⋃ n : ℕ, D.delta^[n] '' s
  have hle : Ideal.span s ≤ Ideal.span t := by
    apply Ideal.span_le.mpr
    intro x hx
    exact Ideal.subset_span (Set.mem_iUnion.mpr ⟨0, x, hx, rfl⟩)
  have hstable : D.IsStable (Ideal.span t) := by
    apply D.isStable_span
    intro x hx
    obtain ⟨n, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
    apply Ideal.subset_span
    exact Set.mem_iUnion.mpr ⟨n + 1, a, ha, Function.iterate_succ_apply' D.delta n a⟩
  apply le_antisymm (D.deltaClosure_le hle hstable)
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
  clear hx
  induction n with
  | zero => exact D.le_deltaClosure _ (Ideal.subset_span ha)
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.isStable_deltaClosure _ _ ih

/-- δ閉包はIのすべての反復δ像で生成されるイデアル（BS 著者版 Example 2.10 の生成元の記述）。
抽象的な交わりによる構成に、具体的な生成元表示を与える。 -/
theorem deltaClosure_eq_span_iterates (D : DeltaStructure p A) (I : Ideal A) :
    D.deltaClosure I = Ideal.span (⋃ n : ℕ, D.delta^[n] '' (I : Set A)) := by
  simpa only [Ideal.span_eq] using
    D.deltaClosure_span_eq_span_generator_iterates (I : Set A)

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaClosureGeneration

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 2.10"] _root_.SerrePositivity.BhattScholze.DeltaStructure.deltaClosure
attribute [cite BS19 "Ex 2.10"] _root_.SerrePositivity.BhattScholze.DeltaStructure.deltaClosure_eq_span_iterates
attribute [cite BS19 "Ex 2.10"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_deltaClosure_quotient_lift
attribute [cite BS19 "Lemma 2.9"] _root_.SerrePositivity.BhattScholze.DeltaStructure.existsUnique_quotient_lift
attribute [cite BS19 "Lemma 2.9"] _root_.SerrePositivity.BhattScholze.DeltaStructure.isStable_iff_existsUnique_quotient
attribute [cite BS19 "Lemma 2.9"] _root_.SerrePositivity.BhattScholze.DeltaStructure.quotient
