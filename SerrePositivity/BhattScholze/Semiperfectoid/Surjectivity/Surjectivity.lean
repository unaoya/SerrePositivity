module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Closure
public import SerrePositivity.BhattScholze.Perfectoidization.WittPushout
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.CompatibleRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.CompatibleRootPerfectoid
public import SerrePositivity.BhattScholze.Perfectoidization.TensorPerfectoidization
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Perfectoidization
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-!
# semiperfectoid 環の perfectoid 化は全射（BS 著者版 Theorem 7.4）

## 概要
導来 p 完備な perfectoid 環の全射商の任意の perfectoid 化は全射。
André の補題（BS 著者版 Theorem 7.14）で絶対整閉な perfectoid 環へ
p 完全忠実平坦に拡大し、根付き拡大での全射性を降下する。旧い適用形（p ねじれのない商）と全射の保存も含む。
BS 著者版 Theorem 7.4 の全射性を述べる。原文の証明中の GR への引用は別文献の結果を指す。

## 方針
核の元が互換 p 冪根を持つ場合の全射性、底変換、p 完全忠実平坦な降下を組み合わせる。

## 規約
André を使わない旧証明は Semiperfectoid/RootEnvelope。

## 使われ方
CLMST、Lemma 10.3、BS 著者版 Proposition 8.13 の環版。
-/

universe u

/-! ## 根付き拡大の剰余テンソルと通常テンソルのmod p

G1と同じ剰余代数構造を使い、Mathlibの基底変更の消去と商テンソルの同型を合成する。
導来テンソルやTorの仮定を使わない通常テンソルの比較。
-/

@[expose] public noncomputable section TensorResidueBaseChangeComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
attribute [local instance] principalAdicQuotientAlgebra
variable (p : ℕ) (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- 根付き拡大の正確な剰余テンソルを、通常テンソルをpで割った商へ同定する。 -/
def Semiperfectoid.tensorResidueBaseChangeEquiv :
    ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T) ⊗[R ⧸ Ideal.span {(p : R)}]
      (S ⧸ Ideal.span {algebraMap R S (p : R)}) ≃+*
      (S ⊗[R] T) ⧸ Ideal.span {(p : S ⊗[R] T)} := by
  let Q := R ⧸ Ideal.span {(p : R)}
  let U := S ⧸ Ideal.span {algebraMap R S (p : R)}
  let e1 := (Algebra.TensorProduct.comm Q (Q ⊗[R] T) U).toRingEquiv
  let : IsScalarTower R Q U := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let e2 := (Algebra.TensorProduct.cancelBaseChange R Q Q U T).toRingEquiv
  let e3 := (Algebra.TensorProduct.quotientTensorEquiv (R := R) R T S
    (Ideal.span {algebraMap R S (p : R)})).toRingEquiv
  have hI : (Ideal.span {algebraMap R S (p : R)}).map (algebraMap S (S ⊗[R] T)) =
      Ideal.span {(p : S ⊗[R] T)} := by
    simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  exact e1.trans (e2.trans (e3.trans (Ideal.quotEquivOfEq hI)))

/-- 比較同型の純粋テンソルの代表元上の式。 -/
@[simp] theorem Semiperfectoid.tensorResidueBaseChangeEquiv_tmul_mk (r : R) (s : S) (t : T) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R S T
      ((Ideal.Quotient.mk _ r ⊗ₜ[R] t) ⊗ₜ[R ⧸ Ideal.span {(p : R)}]
        Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ ((algebraMap R S r * s) ⊗ₜ[R] t) := by
  simp [_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv, Algebra.smul_def]
  rfl

variable {C : Type u} [CommRing C] [Algebra R C]

/-- 比較同型は根付き拡大の線形テンソル射と通常テンソルの標準mod p射を結ぶ。 -/
theorem Semiperfectoid.tensorResidueBaseChangeEquiv_natural [Fact p.Prime] (f : S →ₐ[R] C)
    (x : ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T) ⊗[R ⧸ Ideal.span {(p : R)}]
      (S ⧸ Ideal.span {algebraMap R S (p : R)})) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R C T
      (((_root_.SerrePositivity.principalAdicReductionMap (p : R) f).lTensor
        ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T)) x) =
      _root_.SerrePositivity.modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R S T x) := by
  refine TensorProduct.inductionOn x (fun e s ↦ ?_) (fun x y hx hy ↦ ?_)
  · refine TensorProduct.inductionOn e (fun r t ↦ ?_) (fun e e' he he' ↦ ?_)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [LinearMap.lTensor_tmul, _root_.SerrePositivity.principalAdicReductionMap_mk,
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv_tmul_mk, _root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv_tmul_mk]
      change Ideal.Quotient.mk _ ((algebraMap R C r * f s) ⊗ₜ[R] t) =
        Ideal.Quotient.mk _ (f (algebraMap R S r * s) ⊗ₜ[R] t)
      rw [map_mul, f.commutes]
    · simp only [TensorProduct.add_tmul, map_add, he, he']
  · simp only [map_add, hx, hy]

/-- 通常テンソルのmod p全射性を、根付き拡大の正確な剰余テンソル線形射へ移す。 -/
theorem Semiperfectoid.surjective_principalResidueTensor_of_modP_tensorMap [Fact p.Prime]
    (f : S →ₐ[R] C)
    (h : Function.Surjective
      (_root_.SerrePositivity.modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom)) :
    Function.Surjective ((_root_.SerrePositivity.principalAdicReductionMap (p : R) f).lTensor
      ((R ⧸ Ideal.span {(p : R)}) ⊗[R] T)) := by
  intro y
  obtain ⟨x, hx⟩ := h (_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R C T y)
  refine ⟨(_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R S T).symm x,
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R C T).injective ?_⟩
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv_natural,
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorResidueBaseChangeEquiv p R S T).apply_symm_apply]
  exact hx

end SerrePositivity.BhattScholze

end TensorResidueBaseChangeComparison

/-! ## 根付き拡大によるperfectoid化の全射性降下

mod pのテンソル射の全射性を入力とし、既存の忠実平坦降下を適用する。
完備底変換との比較・その射の全射性は別工程の仮定であり、自動とはしない。
-/

@[expose] public noncomputable section PerfectoidizationSurjectivityDescent

namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
attribute [local instance] principalAdicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {R S C R' : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing R']
variable [Algebra R S] [Algebra R C] [Algebra R R']

/-- 導来p完備な源のperfectoid化は、p完全忠実平坦拡大後のmod p全射性から全射になる。
通常のR'の忠実平坦性や源のp正則性は要求しない。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_residue_baseChange
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) R')
    (h : Function.Surjective
      ((_root_.SerrePositivity.principalAdicReductionMap (p : R) f).lTensor
        ((R ⧸ Ideal.span {(p : R)}) ⊗[R] R'))) : Function.Surjective f := by
  have hrec := (_root_.SerrePositivity.DerivedCompletion.isModuleComplete_iff_recurrence_bijective
    S (p : S) (ModuleCat.of S S)).mp hS
  have hpre : IsPrecomplete (Ideal.span {(p : S)}) S :=
    _root_.SerrePositivity.isPrecomplete_of_adicRecurrenceMap_surjective (p : S) hrec.2
  let : IsPrecomplete (Ideal.span {algebraMap R S (p : R)}) S := by
    have he : algebraMap R S (p : R) = (p : S) := map_natCast _ p
    rw [he]
    exact hpre
  let := hf.1.isAdicComplete C p
  let : IsHausdorff (Ideal.span {algebraMap R C (p : R)}) C := by
    have he : algebraMap R C (p : R) = (p : C) := map_natCast _ p
    rw [he]
    infer_instance
  let := hflat.2
  exact _root_.SerrePositivity.surjective_algHom_of_principal_residue_baseChange (p : R) R' f h

end SerrePositivity.BhattScholze

end PerfectoidizationSurjectivityDescent

/-! ## 全射商の通常底変換の核

全射algebraMap R Sの核をTへ拡張したイデアルが、T→S⊗[R]Tの実際の核である。
平坦性・完備性・有限生成性は要求しない。根付き生成族の入力の接続に使う。
-/

@[expose] public noncomputable section TensorBaseChangeKernel

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- 全射商を通常底変換した標準射の核は、元の核の拡張イデアル。 -/
theorem Semiperfectoid.tensorBaseChangeKernel_eq_map (hq : Function.Surjective (algebraMap R S)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R T) := by
  let J := RingHom.ker (algebraMap R S)
  let I := J.map (algebraMap R T)
  let U := T ⧸ I
  let qU := Ideal.Quotient.mk I
  have hle : J ≤ RingHom.ker (qU.comp (algebraMap R T)) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let g := (algebraMap R S).liftOfSurjective hq ⟨qU.comp (algebraMap R T), hle⟩
  have hg (r : R) : g (algebraMap R S r) = qU (algebraMap R T r) :=
    RingHom.liftOfSurjective_comp_apply _ _ _ r
  let L := _root_.SerrePositivity.coefficientTensorLift g qU hg
  let iT := (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  apply le_antisymm
  · intro t ht
    have hL : L (iT t) = qU t := by
      change _root_.SerrePositivity.coefficientTensorLift g qU hg ((1 : S) ⊗ₜ[R] t) = qU t
      rw [_root_.SerrePositivity.coefficientTensorLift_tmul, map_one, one_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change iT t = 0 at ht
    rw [← hL, ht, map_zero]
  · change J.map (algebraMap R T) ≤ RingHom.ker iT
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change iT (algebraMap R T r) = 0
    change algebraMap R S r = 0 at hr
    calc
      iT (algebraMap R T r) =
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) (algebraMap R S r) :=
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes r).trans
          ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r).symm
      _ = 0 := by rw [hr, map_zero]

/-- 元の核の生成族の像を初項とする族は、通常底変換の核を初項イデアルとして生成する。
この核の同定自体には、後続項が根であることは必要ない。 -/
theorem Semiperfectoid.tensorBaseChangeKernel_eq_rootFamilyZeroIdeal
    (hq : Function.Surjective (algebraMap R S))
    {σ : Type u} (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s)) :
    RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom =
      _root_.SerrePositivity.compatibleRootFamilyZeroIdeal ρ := by
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorBaseChangeKernel_eq_map hq, ha, Ideal.map_span, ← Set.range_comp]
  unfold _root_.SerrePositivity.compatibleRootFamilyZeroIdeal
  congr 1
  exact congrArg Set.range (funext hρ0).symm

end SerrePositivity.BhattScholze

end TensorBaseChangeKernel

/-! ## 任意イデアルの全元が根を持つ場合の全射性

有限生成への帰着を使わず、Jの全元を根族の添字とする。
根付き拡大の存在はこの定理の仮定であり、Andréの引用は使わない。
-/

@[expose] public noncomputable section RootedIdealSurjectivity

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの各元を最初の元に持つ根族は、最初の元のイデアルとしてJそのものを生成する。 -/
theorem Semiperfectoid.compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal
    (J : Ideal R) (ρ : J → ℕ → R) (hρ0 : ∀ s, ρ s 0 = (s : R)) :
    _root_.SerrePositivity.compatibleRootFamilyZeroIdeal ρ = J := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change ρ s 0 ∈ J
    rw [hρ0]
    exact s.property
  · intro x hx
    have hh : ρ ⟨x, hx⟩ 0 = x := hρ0 ⟨x, hx⟩
    rw [← hh]
    exact Ideal.mem_span_range_self

/-- 任意イデアルの全元が両立する根を持てば、その商の任意の普遍perfectoid化は全射。
元族・イデアルの有限生成性、商のp正則性・完備性を仮定しない。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_rootedIdeal
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (J : Ideal R) (ρ : J → ℕ → R)
    (hρ0 : ∀ s, ρ s 0 = (s : R)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {C : Type u} [CommRing C] (f : R ⧸ J →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) :
    Function.Surjective f := by
  have hJ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal J ρ hρ0
  let e : R ⧸ J ≃+* R ⧸ _root_.SerrePositivity.compatibleRootFamilyZeroIdeal ρ := Ideal.quotEquivOfEq hJ.symm
  let ff := f.comp e.symm.toRingHom
  have hff : _root_.SerrePositivity.IsPerfectoidization p ff := hf.precomp_ringEquiv e.symm
  have hsurj := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_compatibleRootFamily hR ρ hρ ff hff
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨e.symm y, hy⟩

end SerrePositivity.BhattScholze

end RootedIdealSurjectivity

/-! ## 根を持つ核を持つ全射商のperfectoid化

全射な環準同型を、その実際の核の商に同定して根付きイデアルの結果を適用する。
一般全射商の全射性を引用せず、核の両立する根を明示して入力する。
-/

@[expose] public noncomputable section RootedKernelSurjectivity

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- perfectoid環の全射商の核の各元が両立する根を持てば、任意のperfectoid化は全射。
商の完備性・p正則性・核の有限生成性は要求しない。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_rootedKernel
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (ρ : RingHom.ker q → ℕ → R) (hρ0 : ∀ s, ρ s 0 = (s : R))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  let e : R ⧸ RingHom.ker q ≃+* S := RingHom.quotientKerEquivOfSurjective hq
  have hfe : _root_.SerrePositivity.IsPerfectoidization p (f.comp e.toRingHom) := hf.precomp_ringEquiv e
  have hs := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_rootedIdeal hR (RingHom.ker q)
    ρ hρ0 hρ (f.comp e.toRingHom) hfe
  intro c
  obtain ⟨x, hx⟩ := hs c
  exact ⟨e x, hx⟩

end SerrePositivity.BhattScholze

end RootedKernelSurjectivity

/-! ## 根付き底変換後の全射性と標準mod pテンソル射

全射商の通常底変換の標準射を、根を持つ実際の核の補題へ接続する。
根付き拡大の存在・忠実平坦性・最終降下は別工程。
-/

@[expose] public noncomputable section RootedTensorBaseChangeSurjectivity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {R S C T E : Type u} [CommRing R] [CommRing S] [CommRing C]
variable [CommRing T] [CommRing E] [Algebra R S] [Algebra R C] [Algebra R T]

/-- 全射商を底変換した核が根を持てば、底変換したperfectoid化の合成射は全射。
商の完備性・有限生成性・p正則性を要求しない。 -/
theorem Semiperfectoid.surjective_perfectoidizationTensorBaseChangeMap_of_rootedKernel
    (p : ℕ) [Fact p.Prime] (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : _root_.SerrePositivity.IsPerfectoidization p F) :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap f F) := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_rootedKernel hT
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
    (Algebra.TensorProduct.includeRight_surjective T hq) ρ hρ0 hρ
    (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap f F)
    (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf F hF)

/-- 同じ根付き入力とFの標準mod p比較から、通常テンソル射のmod p全射性を得る。
これを根付き拡大の剰余テンソル射へ運ぶ図式と忠実平坦降下は別工程。 -/
theorem Semiperfectoid.surjective_modP_tensorMap_of_rootedKernel
    (p : ℕ) [Fact p.Prime] (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : _root_.SerrePositivity.IsPerfectoidization p F)
    (hbij : Function.Bijective (_root_.SerrePositivity.modPMap p F)) :
    Function.Surjective
      (_root_.SerrePositivity.modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
  have hsurj := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_perfectoidizationTensorBaseChangeMap_of_rootedKernel p
    hT hq ρ hρ0 hρ f hf F hF
  intro y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hsurj (F c)
  refine ⟨Ideal.Quotient.mk _ x, hbij.injective ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(p : E)})
    (F (Algebra.TensorProduct.map f (AlgHom.id R T) x)) =
      Ideal.Quotient.mk (Ideal.span {(p : E)}) (F c)
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : E)})) hx

/-- 任意perfectoid基底と根付き核を持つperfectoid拡大に対し、
標準通常テンソル射のmod pは全射。具体的Witt余積の存在と比較を内部で供給する。 -/
theorem Semiperfectoid.surjective_modP_tensorMap_of_rootedPerfectoidBaseChange
    (p : ℕ) [Fact p.Prime] (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) (hq : Function.Surjective (algebraMap R S))
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom) :
    Function.Surjective
      (_root_.SerrePositivity.modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
  obtain ⟨E, hE, F, hF, hbij, _⟩ := _root_.SerrePositivity.BhattScholze.exists_perfectoidizationTensorBaseChange p hR hT f hf
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_modP_tensorMap_of_rootedKernel p hT hq ρ hρ0 hρ f hf F hF hbij

end SerrePositivity.BhattScholze

end RootedTensorBaseChangeSurjectivity

/-! ## 根付き完全忠実平坦perfectoid拡大からの全射性降下

Witt余積・通常mod p比較・G1を合成する。拡大の存在は仮定として明示する。
André引用を使わずに、任意の拡大データに相対的な公開定理を証明する。
-/

@[expose] public noncomputable section RootedPerfectoidSurjectivityDescent

namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {R S C T : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing T]
variable [Algebra R S] [Algebra R C] [Algebra R T]

/-- 根付き核を持つp完全忠実平坦perfectoid拡大があれば、導来p完備な全射商の
任意perfectoid化は全射。p正則性・有限性・古典的完備性を新しく仮定しない。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_rootedPerfectoidBaseChange
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (ρ : RingHom.ker
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = (s : T)) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  have hmod := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_modP_tensorMap_of_rootedPerfectoidBaseChange p hR hT hq
    ρ hρ0 hρ f hf
  have hres := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_principalResidueTensor_of_modP_tensorMap p R S T f hmod
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_residue_baseChange f hf hS hflat hres

/-- 拡大の各元の両立するp冪根を入力する全射性降下。拡大の存在は結論に含めない。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_allRootsPerfectoidBaseChange
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (hroots : ∀ a : T, ∃ ρ : ℕ → T, ρ 0 = a ∧ ∀ n, ρ (n + 1) ^ p = ρ n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  let J := RingHom.ker (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
  have h : ∀ a : J, ∃ ρ : ℕ → T, ρ 0 = (a : T) ∧ ∀ n, ρ (n + 1) ^ p = ρ n :=
    fun a ↦ hroots a
  choose ρ hρ0 hρ using h
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_rootedPerfectoidBaseChange hR hT hq
    hS hflat ρ hρ0 hρ f hf

/-- 拡大が整代数的閉なら既存の根の補題で必要な根を供給できる。
完全忠実平坦perfectoidな整代数的閉拡大の存在は依然として入力。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_aicPerfectoidBaseChange
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (haic : _root_.SerrePositivity.IsAbsolutelyIntegrallyClosed T)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_allRootsPerfectoidBaseChange hR hT hq hS hflat
    (fun a ↦ haic.exists_compatible_pow_roots (Fact.out : p.Prime).pos a) f hf

end SerrePositivity.BhattScholze

end RootedPerfectoidSurjectivityDescent

/-! ## semiperfectoid 環の一般の全射性：André の補題による原典の証明

André の補題（BS 著者版 Theorem 7.14、`Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、
証明済み）による、原典の BS 著者版 Theorem 7.4 の証明。
絶対整閉な perfectoid 環への p 完全忠実平坦な拡大で全射性を得て、元の基底へ降下する。
-/

@[expose] public noncomputable section AndreSurjectivity

namespace SerrePositivity.BhattScholze

/-- 半 perfectoid 商の普遍 perfectoid 化の単位は全射（BS 著者版 Theorem 7.4 の André の補題による証明、序論の Theorem 1.12 (2)）。
方針：André の補題（BS 著者版 Theorem 7.14）で完全忠実平坦な試験拡大を取る。
導来p完備な全射商の任意perfectoid化は全射であり、一般pねじれ商を含む。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_andre
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    (p : ℕ) [Fact p.Prime] (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p)
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨T, hTring, hTalg, hT, hflat, haic⟩ :=
    _root_.SerrePositivity.BhattScholze.Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed R p hR
  let := hTring
  let := hTalg
  let : Algebra R S := q.toAlgebra
  let : Algebra R C := (f.comp q).toAlgebra
  let ff : S →ₐ[R] C := { f with commutes' := fun _ ↦ rfl }
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_aicPerfectoidBaseChange hR hT hq hS
    hflat haic ff hf

end SerrePositivity.BhattScholze

end AndreSurjectivity

/-! ## 導来p完備なperfectoid環の全射商の普遍perfectoid化は全射

## 概要
BS 著者版 Theorem 7.4。perfectoid 環 R の導来 p 完備な全射商 S の任意の perfectoid 化は全射。

## 方針
原典どおり、André の補題（BS 著者版 Theorem 7.14、証明済み）で絶対整閉な perfectoid 環 T へ
p 完全忠実平坦に拡大する。T では核の全元が両立する p 冪根を持つので全射性が出て、
それを R へ降下する（`Semiperfectoid/Surjectivity/Surjectivity`）。

## 規約
p ねじれなし・有限性・古典的完備性は仮定しない。André を使わない別証明は
`Semiperfectoid/Surjectivity/RootEnvelope/PerfectPrism`。

## 使われ方
CLMST、`Almost/Lemma103`、`Perfectoidization/CompletedBaseChange`、
`Semiperfectoid/Surjectivity/Surjectivity`、`Semiperfectoid/Surjectivity/Surjectivity` で使う。
-/

@[expose] public noncomputable section SemiperfectoidSurjectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 任意perfectoid環の導来p完備な全射商の、任意の普遍perfectoid化は全射（BS 著者版 Theorem 7.4、序論の Theorem 1.12 (2)）。
pねじれのない商・有限性・古典的完備性は仮定しない。証明は André の補題経由。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_andre R S C p hR q hq hS f hf

/-- 導来 p 完備な半 perfectoid 商は全射な perfectoid 化を持つ
（BS 著者版 Theorem 7.4 と Corollary 7.3 の第一文、序論の Theorem 1.12 (2)）。 -/
theorem Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C),
      _root_.SerrePositivity.IsPerfectoidization p f ∧ Function.Surjective f := by
  obtain ⟨C, hC, f, hf⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient hR q hq hS
  let := hC
  exact ⟨C, hC, f, hf,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq hS f hf⟩

/-- 古典的p進完備な商への互換入口。共通の比較により商のp正則性は不要。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_adic_complete_quotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR q hq
    (_root_.SerrePositivity.DerivedCompletion.isModuleComplete_of_isAdicComplete S (p : S) (ModuleCat.of S S)) f hf

end SerrePositivity.BhattScholze

end SemiperfectoidSurjectivity

/-! ## semiperfectoid全射性の証明済み互換入口

BS 著者版 Corollary 7.3 / BS 著者版 Theorem 7.4の、pねじれのない古典的p進完備商への旧適用形。
任意perfectoid源の導来p完備全射商に対する一般全射性とB3の存在・普遍性から証明する。
古典的/導来完備性の比較は既存共通APIを使用する。公開署名を維持し、文献入力のsorryは解消済み。

出典：https://people.mpim-bonn.mpg.de/scholze/prisms.pdf （§7.1、印刷pp.55–56）。
-/

public section TorsionFreeQuotientSurjectivity

namespace SerrePositivity.BhattScholze.Inputs

/-- BS 著者版 Corollary 7.3 / BS 著者版 Theorem 7.4のpねじれのない完備商への適用形。 -/
theorem exists_surjective_perfectoidization_of_complete_torsionFree_quotient
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hp : Function.Injective (fun x : S ↦ (p : S) * x)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C),
      IsPerfectoidization p f ∧ Function.Surjective f := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient hR q hq
    ((DerivedCompletion.isModuleComplete_iff_isAdicComplete_of_regular S (p : S)
      (ModuleCat.of S S) hp).mpr inferInstance)

end SerrePositivity.BhattScholze.Inputs

end TorsionFreeQuotientSurjectivity

/-! ## 証明済みsemiperfectoid全射性から任意の普遍対象への移送 -/

public section PerfectoidizationSurjectivity

namespace SerrePositivity.BhattScholze

/-- 証明済みの全射perfectoid化から、任意の普遍perfectoid化へ全射性を移す。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_complete_torsionFree_quotient
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    (hp : Function.Injective (fun x : S ↦ (p : S) * x))
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨D, hD, g, hg, hgs⟩ :=
    _root_.SerrePositivity.BhattScholze.Inputs.exists_surjective_perfectoidization_of_complete_torsionFree_quotient R S p hR q hq hp
  let := hD
  exact (hg.surjective_iff p hf).mp hgs

end SerrePositivity.BhattScholze

end PerfectoidizationSurjectivity

/-! ## Perfectoidization preserves surjective maps

The actual functorial map has complete image. Its inclusion into the target is
again a universal perfectoidization, so B4 makes this inclusion surjective.
-/

@[expose] public noncomputable section PerfectoidizationSurjectiveMap

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- Every actual map between universal perfectoidizations induced by a
surjection is surjective. No completeness is assumed on the original rings. -/
theorem Semiperfectoid.perfectoidization_map_surjective_of_surjective
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C} {g : B →+* D}
    (hf : _root_.SerrePositivity.IsPerfectoidization p f) (hg : _root_.SerrePositivity.IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q) :
    Function.Surjective (_root_.SerrePositivity.IsPerfectoidization.map hf hg q) := by
  let m := _root_.SerrePositivity.IsPerfectoidization.map hf hg q
  let S := m.range
  let π : C →+* S := m.rangeRestrict
  let ι : S →+* D := m.range.subtype
  have hπ : Function.Surjective π := m.rangeRestrict_surjective
  have hcomm : m.comp f = g.comp q := hf.map_comp hg q
  have hb : ∀ b, g b ∈ m.range := by
    intro b
    obtain ⟨a, rfl⟩ := hq b
    exact ⟨f a, RingHom.congr_fun hcomm a⟩
  let b : B →+* S := g.codRestrict m.range hb
  have hi : _root_.SerrePositivity.IsPerfectoidization p ι := by
    refine ⟨hg.1, ?_⟩
    intro T _ hT k
    obtain ⟨l, hl, huniq⟩ := hg.2 T hT (k.comp b)
    have hlm : l.comp m = k.comp π := by
      apply (hf.2 T hT ((k.comp π).comp f)).unique
      · ext a
        have he := RingHom.congr_fun hl (q a)
        change l (g (q a)) = k (b (q a)) at he
        have hba : b (q a) = π (f a) := by
          apply Subtype.ext
          exact (RingHom.congr_fun hcomm a).symm
        change l (m (f a)) = k (π (f a))
        have hma : m (f a) = g (q a) := RingHom.congr_fun hcomm a
        rw [hma, ← hba]
        exact he
      · rfl
    refine ⟨l, ?_, ?_⟩
    · ext s
      obtain ⟨c, rfl⟩ := hπ s
      exact RingHom.congr_fun hlm c
    · intro l' hl'
      apply huniq
      ext x
      exact RingHom.congr_fun hl' (b x)
  let := hf.1.isAdicComplete C p
  let := hg.1.isAdicComplete D p
  let : IsAdicComplete (Ideal.span {(p : S)}) S := _root_.SerrePositivity.isAdicComplete_ringHom_range p m
  have hι := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_adic_complete_quotient hf.1 π hπ ι hi
  intro d
  obtain ⟨s, hs⟩ := hι d
  obtain ⟨c, hc⟩ := hπ s
  exact ⟨c, by change ι (π c) = d; rw [hc, hs]⟩

end SerrePositivity.BhattScholze

end PerfectoidizationSurjectiveMap

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 1.12" (partial := special) "(1) Prop 7.2（全 prism の中の始対象）は本体になく不要（D37、代数的部分だけ Delta/Division）。(2) Cor 7.3・Thm 7.4 は本体で sorry なし（完全試験 prism への始性で構成、超限構成は経由しない） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient
attribute [cite BS19 "Thm 7.4"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_surjective_perfectoidization_of_semiperfectoid_quotient
attribute [cite BS19 "Thm 7.4"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_andre
attribute [cite BS19 "Thm 7.4"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_semiperfectoid_quotient
