module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
概要：完全な増大鎖複体の核による尾部の分解。
方針：第1次数のサイクルを新しい第0項とし、元の微分をサイクルへ因子分解する。
規約：核・全射・完全性は元の複体の完全性から証明する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限次元移動。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [Category.{v} A] [Abelian A] (K : ChainComplex A ℕ)

/--
概要：第1次数の核を増大先とする分解の尾部を構成する。
方針：最初の微分だけをサイクルへの因子分解に置き換える。
規約：新しい第n+1項は元の第n+2項。
使われ方：TT §3、Toën §3.2 の Ext の次元移動。
-/
def cycleResolutionTail : ChainComplex A ℕ :=
  ChainComplex.of
    (fun n => match n with
      | 0 => K.cycles 1
      | n + 1 => K.X (n + 2))
    (fun n => match n with
      | 0 => K.toCycles 2 1
      | n + 1 => K.d (n + 3) (n + 2))
    (by
      intro n
      cases n with
      | zero => exact K.d_toCycles 3 2 1
      | succ n => exact K.d_comp_d _ _ _)

/--
概要：完全な複体では第2項から第1サイクルへの微分の因子分解は epi。
方針：指定した短複体の完全性とサイクルの比較同型を使う。
規約：実際の toCycles 写像について証明する。
使われ方：TT §3、Toën §3.2 の尾部の増大の全射性。
-/
lemma resolution_toCycles_epi (hK : K.ExactAt 1) : Epi (K.toCycles 2 1) := by
  let e := K.cyclesIsoSc' 2 1 0 (by simp) (by simp)
  have hs : (K.sc' 2 1 0).Exact :=
    (HomologicalComplex.exactAt_iff' K 2 1 0 (by simp) (by simp)).mp hK
  have : Epi (K.toCycles 2 1 ≫ e.hom) := by
    rw [HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    exact hs.epi_toCycles
  have : Epi ((K.toCycles 2 1 ≫ e.hom) ≫ e.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this

/--
概要：完全な増大鎖複体の第1サイクル・第1項・第0項の短複体。
方針：サイクルの包含と元の最初の微分を使う。
規約：新たな核対象を独立に選ばない。
使われ方：TT §3、Toën §3.2 の次元移動の短完全列。
-/
def resolutionKernelShortComplex : ShortComplex A :=
  ShortComplex.mk (K.iCycles 1) (K.d 1 0) (K.iCycles_d 1 0)

/--
概要：完全な増大鎖複体の第1核の短複体は短完全列。
方針：サイクルの核の普遍性と零次数の完全性から mono・epi を得る。
規約：短完全性を入力のフィールドにしない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の次元移動。
-/
lemma resolutionKernelShortComplex_shortExact (hK : K.Acyclic) :
    (resolutionKernelShortComplex K).ShortExact := by
  have hs := (HomologicalComplex.exactAt_iff' K 1 0 0 (by simp) (by simp)).mp (hK 0)
  have : Epi (K.d 1 0) := (ShortComplex.exact_iff_epi _ (by simp)).mp hs
  exact
    { exact := (resolutionKernelShortComplex K).exact_of_f_is_kernel
        (K.cyclesIsKernel 1 0 (by simp))
      mono_f := by change Mono (K.iCycles 1); infer_instance
      epi_g := by change Epi (K.d 1 0); infer_instance }

/--
概要：完全な増大鎖複体の第1サイクルで増大した尾部は全次数で完全。
方針：零次数はサイクルへの全射、次の次数は核の包含で完全性を反映し、それ以降は元の複体を使う。
規約：尾部の完全性を新たな仮定にしない。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の有限次元移動の帰納。
-/
lemma cycleResolutionTail_acyclic (hK : K.Acyclic) : (cycleResolutionTail K).Acyclic := by
  intro n
  cases n with
  | zero =>
    have : Epi (K.toCycles 2 1) := resolution_toCycles_epi K (hK 1)
    apply (HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)).mpr
    apply (ShortComplex.exact_iff_epi _ (by simp [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc])).mpr
    simpa [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using this
  | succ n =>
    cases n with
    | zero =>
      apply (HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)).mpr
      let T := (cycleResolutionTail K).sc' 2 1 0
      let S := K.sc' 3 2 1
      let φ : T ⟶ S :=
        { τ₁ := 𝟙 (K.X 3)
          τ₂ := 𝟙 (K.X 2)
          τ₃ := K.iCycles 1
          comm₁₂ := by
            simp [T, S, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
              cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc]
          comm₂₃ := by
            simpa [T, S, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
              cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using (K.toCycles_i 2 1).symm }
      have : Epi φ.τ₁ := by change Epi (𝟙 (K.X 3)); infer_instance
      have : IsIso φ.τ₂ := by change IsIso (𝟙 (K.X 2)); infer_instance
      have : Mono φ.τ₃ := by change Mono (K.iCycles 1); infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        ((HomologicalComplex.exactAt_iff' K 3 2 1 (by simp) (by simp)).mp (hK 2))
    | succ n =>
      apply (HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1)
        (by simp) (by simp)).mpr
      have ht := (HomologicalComplex.exactAt_iff' K (n + 4) (n + 3) (n + 2)
        (by simp) (by simp)).mp (hK (n + 3))
      simpa [cycleResolutionTail, ChainComplex.of.d, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        Nat.add_assoc] using ht

/--
概要：鎖複体から対象への Hom の正次数の完全性を射の因子分解で表す。
方針：各次数で消える合成を持つ射が前の項を経由することを要求する。
規約：これは具体的な Hom の完全性の述語であり、分解の存在のフィールドではない。
使われ方：TT §3、Toën §3.2 の Ext の有限次元移動の一般判定。
-/
def chainHomPositiveExact (F : A) : Prop :=
  ∀ (n : ℕ) (f : K.X (n + 1) ⟶ F), K.d (n + 2) (n + 1) ≫ f = 0 →
    ∃ g : K.X n ⟶ F, K.d (n + 1) n ≫ g = f

/--
概要：Hom の正次数の完全性はサイクルで増大した尾部へ移る。
方針：最初の次数では得た射をサイクルの包含へ制限し、残りは元の因子分解を使う。
規約：同じ対象 F についての実際の因子分解を構成する。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の次元移動の帰納。
-/
lemma chainHomPositiveExact_tail {F : A} (hF : chainHomPositiveExact K F) :
    chainHomPositiveExact (cycleResolutionTail K) F := by
  intro n f hf
  cases n with
  | zero =>
    have hf' : K.d 3 2 ≫ f = 0 := by simpa [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using hf
    obtain ⟨g, hg⟩ := hF 1 f hf'
    refine ⟨K.iCycles 1 ≫ g, ?_⟩
    have h : K.toCycles 2 1 ≫ (K.iCycles 1 ≫ g) = f :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ g) (K.toCycles_i 2 1)).trans hg)
    simpa [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using h
  | succ n =>
    have hf' : K.d (n + 4) (n + 3) ≫ f = 0 := by simpa [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using hf
    obtain ⟨g, hg⟩ := hF (n + 2) f hf'
    exact ⟨g, by simpa [cycleResolutionTail, ChainComplex.of.d, Nat.add_assoc] using hg⟩

/--
概要：Hom の正次数が完全なら第1サイクルからの射は第1項へ延長できる。
方針：第2項からのサイクルへの全射を使い、Hom の完全性で得た射を降ろす。
規約：injectivity は仮定せず、与えられた分解の Hom 完全性だけを使う。
使われ方：TT §3、BvdB Thm 3.1.1、Toën §3.2 の Ext¹ の基底段階。
-/
lemma resolution_cycleHom_extend {F : A} (hK : K.ExactAt 1)
    (hF : chainHomPositiveExact K F) (f : K.cycles 1 ⟶ F) :
    ∃ g : K.X 1 ⟶ F, K.iCycles 1 ≫ g = f := by
  have hf : K.d 3 2 ≫ (K.toCycles 2 1 ≫ f) = 0 := by
    rw [← Category.assoc, K.d_toCycles, zero_comp]
  obtain ⟨g, hg⟩ := hF 1 (K.toCycles 2 1 ≫ f) hf
  have : Epi (K.toCycles 2 1) := resolution_toCycles_epi K hK
  refine ⟨g, (cancel_epi (K.toCycles 2 1)).mp ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ g) (K.toCycles_i 2 1)).trans hg)

/--
概要：完全な増大鎖複体の最初の Hom の因子分解は任意の標的について成立する。
方針：第1次数の完全性と零次数の全射性から最初の微分の余核の普遍性を使う。
規約：標的の injectivity は要求しない。
使われ方：TT §3、Toën §3.2 の Čech 分解の Hom 完全性の零次数。
-/
lemma resolution_zeroHom_factor {F : A} (hK : K.Acyclic) (f : K.X 1 ⟶ F)
    (hf : K.d 2 1 ≫ f = 0) : ∃ g : K.X 0 ⟶ F, K.d 1 0 ≫ g = f := by
  have hz := (HomologicalComplex.exactAt_iff' K 1 0 0 (by simp) (by simp)).mp (hK 0)
  have he := (HomologicalComplex.exactAt_iff' K 2 1 0 (by simp) (by simp)).mp (hK 1)
  have : Epi (K.d 1 0) := (ShortComplex.exact_iff_epi _ (by simp)).mp hz
  have : Epi (K.sc' 2 1 0).g := ‹Epi (K.d 1 0)›
  have hc := ((K.sc' 2 1 0).exact_and_epi_g_iff_g_is_cokernel).mp ⟨he, inferInstance⟩
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hc.some f hf
  exact ⟨g, hg⟩

end SerrePositivity.KST.DerivedGeometry
