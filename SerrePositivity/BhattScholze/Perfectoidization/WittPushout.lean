module

public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import SerrePositivity.CommutativeAlgebra.Witt.Lift
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTilt

/-!
# perfectoid 環の Witt 表示の余積

## 概要
共通の Fontaine 生成元による Witt 商表示、Witt 係数テンソルから完備環への普遍射、Witt 商の余積とその mod p。
BS 著者版 Theorem 3.10 の Witt 表示を使って、perfectoid 環の余積を計算する。

## 方針
Witt 係数の余積を Witt 商で割って perfectoid 環の余積の候補を作る。

## 規約
—

## 使われ方
perfectoid 環の通常テンソル積の perfectoid 化。
-/

universe u

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section PerfectCoefficientTensor

namespace SerrePositivity.BhattScholze

-- Preserve rewriting through the former computational definitions.
end SerrePositivity.BhattScholze

end PerfectCoefficientTensor

/-! ## Witt係数テンソルから完備環への普遍射

既存の一般Witt持上げを用いる。完備テンソルを新しく定義せず、
完全係数環のテンソルのWitt環について、p完備試験環への普遍性を証明する。
-/

@[expose] public noncomputable section WittCoefficientPushout

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
variable {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra R A] [Algebra R B]
variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]

private def wittMapResidue {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
    (f : WittVector p k →+* D) : k →+* ModP D p :=
  (WittVector.constantCoeff : WittVector p k →+* k).liftOfSurjective
    (WittVector.constantCoeff_surjective p)
    ⟨(Ideal.Quotient.mk (Ideal.span {(p : D)})).comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_singleton_le_iff_mem]
      change Ideal.Quotient.mk (Ideal.span {(p : D)}) (f (p : WittVector p k)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)⟩

private theorem wittMapResidue_coeff {k : Type u} [CommRing k] [CharP k p]
    [PerfectRing k p] (f : WittVector p k →+* D) (x : WittVector p k) :
    wittMapResidue p f (x.coeff 0) =
      Ideal.Quotient.mk (Ideal.span {(p : D)}) (f x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

private theorem wittMapResidue_teichmuller {k : Type u} [CommRing k] [CharP k p]
    [PerfectRing k p] (f : WittVector p k →+* D) (a : k) :
    wittMapResidue p f a =
      Ideal.Quotient.mk (Ideal.span {(p : D)}) (f (WittVector.teichmuller p a)) := by
  simpa using wittMapResidue_coeff p f (WittVector.teichmuller p a)

omit [CharP R p] [CharP A p] [CharP B p]
  [PerfectRing R p] [PerfectRing A p] [PerfectRing B p] in
/-- 両因子のWitt射は、基底のWitt環上で一致する。 -/
theorem wittCoefficientTensor_base_agreement :
    (WittVector.map (p := p)
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom).comp
        (WittVector.map (algebraMap R A)) =
    (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).comp
        (WittVector.map (algebraMap R B)) := by
  apply RingHom.ext
  intro x
  apply WittVector.ext
  intro n
  simp only [RingHom.comp_apply, WittVector.map_coeff, AlgHom.toRingHom_eq_coe]
  exact (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).commutes (x.coeff n) |>.trans
    ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).commutes (x.coeff n)).symm

variable [CharP (A ⊗[R] B) p] [PerfectRing (A ⊗[R] B) p]

omit [CharP R p] [CharP A p] [CharP B p]
  [PerfectRing R p] [PerfectRing A p] [PerfectRing B p] in
/-- 係数テンソルのWitt環からp Hausdorff環への射は両因子で決まる。 -/
theorem wittCoefficientTensorHom_ext [IsHausdorff (Ideal.span {(p : D)}) D]
    (f g : WittVector p (A ⊗[R] B) →+* D)
    (hA : f.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) =
      g.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom))
    (hB : f.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      g.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)) : f = g := by
  have hres : wittMapResidue p f = wittMapResidue p g := by
    apply RingHom.ext
    intro x
    refine TensorProduct.inductionOn x (fun a b ↦ ?_) (fun x y hx hy ↦ ?_)
    · let iA := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
      let iB := (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
      have ht : a ⊗ₜ[R] b = iA a * iB b := by
        change a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have ha : wittMapResidue p f (iA a) = wittMapResidue p g (iA a) := by
        rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
        have he := RingHom.congr_fun hA (WittVector.teichmuller p a)
        simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
          congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
      have hb : wittMapResidue p f (iB b) = wittMapResidue p g (iB b) := by
        rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
        have he := RingHom.congr_fun hB (WittVector.teichmuller p b)
        simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
          congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
      rw [ht, map_mul, map_mul, ha, hb]
    · simp only [map_add, hx, hy]
  apply wittLift_unique
  apply RingHom.ext
  intro x
  change Ideal.Quotient.mk _ (f x) = Ideal.Quotient.mk _ (g x)
  rw [← wittMapResidue_coeff p f x, ← wittMapResidue_coeff p g x, hres]

omit [CharP R p] [PerfectRing R p] in
/-- 完全係数テンソルのWitt環は、任意のp完備環への両立するWitt射を一意に延長する。
終域のp正則性・非零性は要求しない。 -/
theorem existsUnique_wittCoefficientTensorLift
    [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : WittVector p A →+* D) (g : WittVector p B →+* D)
    (h : f.comp (WittVector.map (algebraMap R A)) =
      g.comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittVector p (A ⊗[R] B) →+* D,
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f ∧
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
  let sA := wittMapResidue p f
  let sB := wittMapResidue p g
  have hs : ∀ r : R, sA (algebraMap R A r) = sB (algebraMap R B r) := by
    intro r
    rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
    have he := RingHom.congr_fun h (WittVector.teichmuller p r)
    simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
      congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
  let s := _root_.SerrePositivity.coefficientTensorLift sA sB hs
  obtain ⟨L, hL, _⟩ := existsUnique_wittResidueLift_of_complete p D (A ⊗[R] B) s
  have hLA : L.comp (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hL (WittVector.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom x)
    change Ideal.Quotient.mk _ (L (WittVector.map _ x)) = _ at hx ⊢
    rw [hx]
    change s (x.coeff 0 ⊗ₜ[R] (1 : B)) = _
    rw [_root_.SerrePositivity.coefficientTensorLift_tmul, map_one, mul_one]
    exact wittMapResidue_coeff p f x
  have hLB : L.comp (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
    apply wittLift_unique
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hL (WittVector.map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom x)
    change Ideal.Quotient.mk _ (L (WittVector.map _ x)) = _ at hx ⊢
    rw [hx]
    change s ((1 : A) ⊗ₜ[R] x.coeff 0) = _
    rw [_root_.SerrePositivity.coefficientTensorLift_tmul, map_one, one_mul]
    exact wittMapResidue_coeff p g x
  refine ⟨L, ⟨hLA, hLB⟩, ?_⟩
  intro M hM
  exact wittCoefficientTensorHom_ext p M L (hM.1.trans hLA.symm) (hM.2.trans hLB.symm)

omit [CharP (A ⊗[R] B) p] [PerfectRing (A ⊗[R] B) p] in
/-- 完全係数環の両立するWitt射の延長。係数テンソルが零環の場合も含む。 -/
theorem existsUnique_wittCoefficientTensorLift_of_perfect
    [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : WittVector p A →+* D) (g : WittVector p B →+* D)
    (h : f.comp (WittVector.map (algebraMap R A)) =
      g.comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittVector p (A ⊗[R] B) →+* D,
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) = f ∧
      L.comp (WittVector.map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) = g := by
  let K := A ⊗[R] B
  rcases subsingleton_or_nontrivial K with hK | hK
  · let := hK
    let sA := wittMapResidue p f
    let sB := wittMapResidue p g
    have hs : ∀ r : R, sA (algebraMap R A r) = sB (algebraMap R B r) := by
      intro r
      rw [wittMapResidue_teichmuller, wittMapResidue_teichmuller]
      have he := RingHom.congr_fun h (WittVector.teichmuller p r)
      simpa only [RingHom.comp_apply, WittVector.map_teichmuller] using
        congrArg (Ideal.Quotient.mk (Ideal.span {(p : D)})) he
    let s := _root_.SerrePositivity.coefficientTensorLift sA sB hs
    have h01 : (1 : ModP D p) = 0 := by
      rw [← s.map_one, Subsingleton.elim (1 : K) 0, s.map_zero]
    have hu : IsUnit (p : D) := by
      apply Ideal.span_singleton_eq_top.mp
      apply (Ideal.eq_top_iff_one _).mpr
      exact Ideal.Quotient.eq_zero_iff_mem.mp h01
    let := subsingleton_of_isUnit_natCast_of_isHausdorff p D hu
    let L : WittVector p K →+* D :=
      { toFun := fun _ ↦ 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    refine ⟨L, ⟨?_, ?_⟩, ?_⟩
    · ext x
      exact Subsingleton.elim _ _
    · ext x
      exact Subsingleton.elim _ _
    · intro M _
      ext x
      exact Subsingleton.elim _ _
  · let := hK
    have hp : (p : K) = 0 := by
      rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero, map_zero]
    let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : PerfectRing K p := _root_.SerrePositivity.perfectCoefficientTensor_perfectRing p R A B
    exact existsUnique_wittCoefficientTensorLift p f g h

end SerrePositivity.BhattScholze

end WittCoefficientPushout

/-! ## 源のFontaine生成元を共用するWitt商表示

非零枝のFontaine写像のデータを入力し、標準写像と両立する具体的商同型を構成する。
源の生成元の像を使うため、余積の両因子の表示に同じ基底生成元を利用できる。
-/

@[expose] public noncomputable section PerfectoidWittBasePresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 源のdistinguished核元の像を使う、終域の標準Witt商表示。 -/
def fontaineBaseWittQuotientEquiv
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    WittVector p (PreTilt S p) ⧸
      Ideal.span {WittVector.map (Perfection.map p (modPMap p f)) d} ≃+* S :=
  (Ideal.quotEquivOfEq (fontaineKernel_eq_span_image_distinguished p f d hd hzero hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (fun x ↦ surjective_fontaineTheta hF x))

/-- 商表示の順射と標準商射の合成は、標準Fontaine写像。 -/
theorem fontaineBaseWittQuotientEquiv_comp_mk
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    (fontaineBaseWittQuotientEquiv p f d hd hzero hF hker).toRingHom.comp
      (Ideal.Quotient.mk _) = WittVector.fontaineTheta S p := by
  apply RingHom.ext
  intro x
  rfl

/-- 商表示の逆射は、標準Fontaine写像を標準商射へ移す。 -/
theorem fontaineBaseWittQuotientEquiv_symm_comp_fontaineTheta
    (f : R →+* S) (d : WittVector p (PreTilt R p))
    (hd : (wittDeltaStructure p (PreTilt R p)).IsDistinguished d)
    (hzero : WittVector.fontaineTheta R p d = 0)
    (hF : Function.Surjective (fun x : ModP S p ↦ x ^ p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal) :
    (fontaineBaseWittQuotientEquiv p f d hd hzero hF hker).symm.toRingHom.comp
      (WittVector.fontaineTheta S p) = Ideal.Quotient.mk _ := by
  let e := fontaineBaseWittQuotientEquiv p f d hd hzero hF hker
  apply RingHom.ext
  intro x
  have he : e (Ideal.Quotient.mk _ x) = WittVector.fontaineTheta S p x :=
    RingHom.congr_fun (fontaineBaseWittQuotientEquiv_comp_mk p f d hd hzero hF hker) x
  change e.symm (WittVector.fontaineTheta S p x) = Ideal.Quotient.mk _ x
  rw [← he, e.symm_apply_apply]

end SerrePositivity.BhattScholze

end PerfectoidWittBasePresentation

/-! ## 共通生成元によるWitt商の余積

完全係数環のテンソルのWitt環を、基底の生成元の像で割る。
係数テンソルが零環になる場合も含めて、候補のperfectoid性と
p完備試験環への普遍性を証明する。導来テンソルの比較とは区別する。
-/

@[expose] public noncomputable section PerfectoidWittPushout

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- 基底Witt元の像で係数テンソルのWitt環を割った環。 -/
abbrev WittCoefficientPushout (d : WittVector p R) :=
  WittVector p (A ⊗[R] B) ⧸ Ideal.span
    {WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
      (WittVector.map (algebraMap R A) d)}

/-- 左因子のWitt商からの標準射。 -/
def wittCoefficientPushoutLeft (d : WittVector p R) :
    (WittVector p A ⧸ Ideal.span {WittVector.map (algebraMap R A) d}) →+*
      WittCoefficientPushout p R A B d := by
  let q : WittVector p (A ⊗[R] B) →+* WittCoefficientPushout p R A B d :=
    Ideal.Quotient.mk _
  let f := q.comp
    (WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom)
  have hk : Ideal.span {WittVector.map (algebraMap R A) d} ≤ RingHom.ker f := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact Ideal.Quotient.lift _ f (fun _ hx ↦ hk hx)

/-- 右因子のWitt商からの標準射。 -/
def wittCoefficientPushoutRight (d : WittVector p R) :
    (WittVector p B ⧸ Ideal.span {WittVector.map (algebraMap R B) d}) →+*
      WittCoefficientPushout p R A B d := by
  let q : WittVector p (A ⊗[R] B) →+* WittCoefficientPushout p R A B d :=
    Ideal.Quotient.mk _
  let f := q.comp
    (WittVector.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)
  have hk : Ideal.span {WittVector.map (algebraMap R B) d} ≤ RingHom.ker f := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change Ideal.Quotient.mk _
      (WittVector.map _ (WittVector.map _ d)) = 0
    have he := RingHom.congr_fun (wittCoefficientTensor_base_agreement p (R := R)
      (A := A) (B := B)) d
    change WittVector.map _ (WittVector.map _ d) =
      WittVector.map _ (WittVector.map _ d) at he
    rw [← he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact Ideal.Quotient.lift _ f (fun _ hx ↦ hk hx)

/-- 左標準射のWitt代表元上の式。 -/
@[simp] theorem wittCoefficientPushoutLeft_mk (d : WittVector p R) (x : WittVector p A) :
    wittCoefficientPushoutLeft p R A B d (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.mk _
      (WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom x) := rfl

/-- 右標準射のWitt代表元上の式。 -/
@[simp] theorem wittCoefficientPushoutRight_mk (d : WittVector p R) (x : WittVector p B) :
    wittCoefficientPushoutRight p R A B d (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.mk _
      (WittVector.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom x) := rfl

/-- 標準射は基底Witt環上で一致する。 -/
theorem wittCoefficientPushout_base_agreement (d : WittVector p R) :
    ((wittCoefficientPushoutLeft p R A B d).comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap R A)) =
    ((wittCoefficientPushoutRight p R A B d).comp (Ideal.Quotient.mk _)).comp
      (WittVector.map (algebraMap R B)) := by
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, wittCoefficientPushoutLeft_mk,
    wittCoefficientPushoutRight_mk]
  exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun
    (wittCoefficientTensor_base_agreement p (R := R) (A := A) (B := B)) x)

variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]

/-- 共通distinguished元によるWitt係数余積はperfectoid。零環の係数テンソルも含む。 -/
theorem wittCoefficientPushout_isIntegralPerfectoid (d : WittVector p R)
    (hd : (wittDeltaStructure p R).IsDistinguished d) :
    IsIntegralPerfectoid (WittCoefficientPushout p R A B d) p := by
  let K := A ⊗[R] B
  rcases subsingleton_or_nontrivial K with hK | hK
  · let := hK
    have : Subsingleton (WittVector p K) := ⟨fun x y ↦ by
      apply WittVector.ext
      intro n
      exact Subsingleton.elim _ _⟩
    exact Or.inl inferInstance
  · let := hK
    have hp : (p : K) = 0 := by
      rw [← map_natCast (algebraMap R K), CharP.cast_eq_zero, map_zero]
    let : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : PerfectRing K p := _root_.SerrePositivity.perfectCoefficientTensor_perfectRing p R A B
    have hA := (wittDeltaStructure_map_isDeltaHom p R (algebraMap R A)).map_isDistinguished hd
    have hK := (wittDeltaStructure_map_isDeltaHom p A
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom).map_isDistinguished hA
    exact wittDistinguishedQuotient_isIntegralPerfectoid p K _ hK

/-- 両因子の共通生成元によるWitt商の射は、p完備な試験環へ一意に延長する。
試験環のp正則性・非零性は要求しない。 -/
theorem existsUnique_wittCoefficientPushoutLift (d : WittVector p R)
    {D : Type u} [CommRing D] [IsAdicComplete (Ideal.span {(p : D)}) D]
    (f : (WittVector p A ⧸ Ideal.span {WittVector.map (algebraMap R A) d}) →+* D)
    (g : (WittVector p B ⧸ Ideal.span {WittVector.map (algebraMap R B) d}) →+* D)
    (h : (f.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap R A)) =
      (g.comp (Ideal.Quotient.mk _)).comp (WittVector.map (algebraMap R B))) :
    ∃! L : WittCoefficientPushout p R A B d →+* D,
      L.comp (wittCoefficientPushoutLeft p R A B d) = f ∧
      L.comp (wittCoefficientPushoutRight p R A B d) = g := by
  obtain ⟨L, ⟨hA, hB⟩, huniq⟩ := existsUnique_wittCoefficientTensorLift_of_perfect p
    (f.comp (Ideal.Quotient.mk _)) (g.comp (Ideal.Quotient.mk _)) h
  let e := WittVector.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
    (WittVector.map (algebraMap R A) d)
  have hzero : L e = 0 := by
    have he := RingHom.congr_fun hA (WittVector.map (algebraMap R A) d)
    change L e = f (Ideal.Quotient.mk _ _) at he
    have hz : Ideal.Quotient.mk (Ideal.span {WittVector.map (algebraMap R A) d})
      (WittVector.map (algebraMap R A) d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [he, hz, map_zero]
  have hk : Ideal.span {e} ≤ RingHom.ker L := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact hzero
  let M := Ideal.Quotient.lift (Ideal.span {e}) L (fun _ hx ↦ hk hx)
  have hMA : M.comp (wittCoefficientPushoutLeft p R A B d) = f := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hA x
  have hMB : M.comp (wittCoefficientPushoutRight p R A B d) = g := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    exact RingHom.congr_fun hB x
  refine ⟨M, ⟨hMA, hMB⟩, ?_⟩
  intro N hN
  apply Ideal.Quotient.ringHom_ext
  change N.comp (Ideal.Quotient.mk _) = L
  apply huniq
  constructor
  · apply RingHom.ext
    intro x
    exact RingHom.congr_fun hN.1 (Ideal.Quotient.mk _ x)
  · apply RingHom.ext
    intro x
    exact RingHom.congr_fun hN.2 (Ideal.Quotient.mk _ x)

end SerrePositivity.BhattScholze

end PerfectoidWittPushout

/-! ## Witt係数余積のmod pと標準射

係数テンソルにCharP pを持つ枝の具体的な同型と、左右の標準射の式。
通常テンソルのmod pとの同型はさらに別工程。
-/

@[expose] public noncomputable section PerfectoidWittPushoutModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CharP R p] [CharP A p] [CharP B p]
variable [PerfectRing R p] [PerfectRing A p] [PerfectRing B p]
variable [CharP (A ⊗[R] B) p]

/-- Witt係数余積のmod pは、係数テンソルを基底生成元の第0係数の像で割った環。 -/
def wittCoefficientPushoutModPEquiv (d : WittVector p R) :
    ModP (WittCoefficientPushout p R A B d) p ≃+*
      (A ⊗[R] B) ⧸ Ideal.span
        {((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom)
          (algebraMap R A (d.coeff 0))} := by
  let : PerfectRing (A ⊗[R] B) p := _root_.SerrePositivity.perfectCoefficientTensor_perfectRing p R A B
  exact wittQuotientModPEquiv p (A ⊗[R] B) _

/-- 同型はWitt代表元の第0係数を標準商へ写す。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_mk (d : WittVector p R)
    (x : WittVector p (A ⊗[R] B)) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ (x.coeff 0) := rfl

/-- 左因子の標準射のmod pでの式。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_left_mk (d : WittVector p R)
    (x : WittVector p A) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _
        (wittCoefficientPushoutLeft p R A B d (Ideal.Quotient.mk _ x))) =
      Ideal.Quotient.mk _ (x.coeff 0 ⊗ₜ[R] (1 : B)) := by
  rw [wittCoefficientPushoutLeft_mk, wittCoefficientPushoutModPEquiv_mk]
  rfl

/-- 右因子の標準射のmod pでの式。 -/
@[simp] theorem wittCoefficientPushoutModPEquiv_right_mk (d : WittVector p R)
    (x : WittVector p B) :
    wittCoefficientPushoutModPEquiv p R A B d
      (Ideal.Quotient.mk _
        (wittCoefficientPushoutRight p R A B d (Ideal.Quotient.mk _ x))) =
      Ideal.Quotient.mk _ ((1 : A) ⊗ₜ[R] x.coeff 0) := by
  rw [wittCoefficientPushoutRight_mk, wittCoefficientPushoutModPEquiv_mk]
  rfl

end SerrePositivity.BhattScholze

end PerfectoidWittPushoutModP
