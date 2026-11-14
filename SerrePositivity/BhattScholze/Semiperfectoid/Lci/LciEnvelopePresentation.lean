module

public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue

/-!
# 自由変数の δ 除算表示

## 概要
自由 δ 環の初期変数を一斉に d で割る通常の δ 包は、商を取る前の
別の自由 δ 環として表示できる。

## 方針
除算の変数と自由変数を対応させ、両方向の合成を普遍性で確認する。

## 規約
BS 著者版 Example 7.9 の普遍自由変数の場合。完備化前の環を使う。

## 使われ方
除算包の Witt 座標による剰余計算を、分類射の自由模型へ移す。
-/

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] {S : Type v}

private theorem freeDelta_hom_ext_initial
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (E : DeltaStructure p B)
    {f g : RelativeFreeDeltaRing (R := A) S →+* B}
    (hf : (relativeFreeDeltaStructure S D).IsDeltaHom E f)
    (hg : (relativeFreeDeltaStructure S D).IsDeltaHom E g)
    (hC : f.comp MvPolynomial.C = g.comp MvPolynomial.C)
    (hX : ∀ s : S, f (MvPolynomial.X (s, 0)) = g (MvPolynomial.X (s, 0))) : f = g := by
  apply MvPolynomial.ringHom_ext' hC
  rintro ⟨s, n⟩
  rw [relativeFreeDeltaHom_X_iterates D E f hf,
    relativeFreeDeltaHom_X_iterates D E g hg, hX]

/-- 概要：初期自由変数の δ 除算包は、除算の解を初期変数とする自由 δ 環。
方針：係数射を x ↦ d x の置換に送り、除算の解を自由変数に送る。逆射は自由性で得る。
規約：BS 著者版 Example 7.9 の普遍置換の未完備な表示。
使われ方：普遍包絡の mod (p,d) の平坦性を既存の Witt 正規化で計算する。 -/
theorem exists_deltaDivision_freeVariable_equiv (D : DeltaStructure p A) (d : A) :
    let U := RelativeFreeDeltaRing (R := A) S
    let DU := relativeFreeDeltaStructure S D
    let x : S → U := fun s => MvPolynomial.X (s, 0)
    let T := DeltaAdjoinDivision DU (MvPolynomial.C d) x
    ∃ e : T ≃+* U,
      (deltaAdjoinDivisionStructure DU (MvPolynomial.C d) x).IsDeltaHom DU e.toRingHom ∧
      e.toRingHom.comp (deltaAdjoinDivisionMap DU (MvPolynomial.C d) x) =
        deltaDivisionSourceMap D d ∧
      ∀ s, e (deltaAdjoinDivisionVariable DU (MvPolynomial.C d) x s) = x s := by
  let U := RelativeFreeDeltaRing (R := A) S
  let DU := relativeFreeDeltaStructure S D
  let C : A →+* U := MvPolynomial.C
  let x : S → U := fun s => MvPolynomial.X (s, 0)
  let T := DeltaAdjoinDivision DU (C d) x
  let DT := deltaAdjoinDivisionStructure DU (C d) x
  let i := deltaAdjoinDivisionMap DU (C d) x
  let y := deltaAdjoinDivisionVariable DU (C d) x
  let a : U →+* U := deltaDivisionSourceMap D d
  have ha : DU.IsDeltaHom DU a := deltaDivisionSourceMap_isDeltaHom D d
  have hi : DU.IsDeltaHom DT i := deltaAdjoinDivisionMap_isDeltaHom DU (C d) x
  have hC : a.comp C = C := RingHom.ext (deltaDivisionSourceMap_C D d)
  have hX (s : S) : a (x s) = C d * x s := by
    simpa only [Function.iterate_zero_apply] using deltaDivisionSourceMap_X D d s 0
  obtain ⟨v, hv, _⟩ := existsUnique_deltaAdjoinDivisionHom DU DU (C d) x a ha x
    (fun s => by
      change a (C d) * x s = a (x s)
      rw [show a (C d) = C d from RingHom.congr_fun hC d, hX s])
  obtain ⟨k, hk, _⟩ := existsUnique_relativeFreeDeltaHom D DT (i.comp C)
    (hi.comp (relativeFreeDeltaStructure_C_isDeltaHom S D)) y
  have hkC : k.comp C = i.comp C := hk.2.1
  have hka : k.comp a = i := by
    apply freeDelta_hom_ext_initial D DT (hk.1.comp ha) hi
    · rw [RingHom.comp_assoc, hC, hkC]
    · intro s
      change k (a (x s)) = i (x s)
      rw [hX s, map_mul]
      exact (congrArg₂ (· * ·) (RingHom.congr_fun hkC d) (hk.2.2 s)).trans
        (deltaAdjoinDivision_relation DU (C d) x s)
  have hvk : v.comp k = RingHom.id U := by
    apply freeDelta_hom_ext_initial D DU (hv.1.comp hk.1) DU.isDeltaHom_id
    · rw [RingHom.comp_assoc, hkC, ← RingHom.comp_assoc, hv.2.1, hC, RingHom.id_comp]
    · intro s
      change v (k (x s)) = x s
      rw [hk.2.2 s, hv.2.2 s]
  have hkv : k.comp v = RingHom.id T := by
    obtain ⟨w, _, hw⟩ := existsUnique_deltaAdjoinDivisionHom DU DT (C d) x i hi y
      (deltaAdjoinDivision_relation DU (C d) x)
    apply (hw _ ⟨hk.1.comp hv.1, ?_, ?_⟩).trans
      (hw _ ⟨DT.isDeltaHom_id, RingHom.id_comp i, fun _ => rfl⟩).symm
    · rw [RingHom.comp_assoc, hv.2.1, hka]
    · intro s
      change k (v (y s)) = y s
      rw [hv.2.2 s, hk.2.2 s]
  have hleft : Function.LeftInverse k v := RingHom.congr_fun hkv
  have hright : Function.RightInverse k v := RingHom.congr_fun hvk
  let e := RingEquiv.ofBijective v ⟨hleft.injective, hright.surjective⟩
  exact ⟨e, hv.1, hv.2.1, hv.2.2⟩

/-- 概要：自由変数を割る置換の mod (p,d) は、始域の初期変数をさらに零にした商上で忠実平坦。
方針：自由変数の除算表示を剰余に移し、Witt 座標の既存のモニック塔を使う。
規約：BS 著者版 Example 7.9 の普遍置換。係数環の p 正則性と δ(d) の単元性を使う。
使われ方：一般の関係列への導来底変換の普遍剰余計算。 -/
theorem exists_deltaDivision_freeVariable_residue_faithfullyFlat
    (D : DeltaStructure p A) (d : A) (hp : Function.Injective (fun x : A => (p : A) * x))
    (u : Aˣ) (hu : (u : A) = D.delta d) :
    let U := RelativeFreeDeltaRing (R := A) S
    let x : S → U := fun s => MvPolynomial.X (s, 0)
    let I : Ideal U := Ideal.span {(p : U), MvPolynomial.C d}
    let J := deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) x
    ∃ b : U ⧸ J →+* U ⧸ I,
      (∀ z : U, b (Ideal.Quotient.mk J z) = Ideal.Quotient.mk I (deltaDivisionSourceMap D d z)) ∧
        letI := b.toAlgebra
        Module.FaithfullyFlat (U ⧸ J) (U ⧸ I) := by
  let U := RelativeFreeDeltaRing (R := A) S
  let C : A →+* U := MvPolynomial.C
  let DU := relativeFreeDeltaStructure S D
  let x : S → U := fun s => MvPolynomial.X (s, 0)
  let I : Ideal U := Ideal.span {(p : U), C d}
  let J := deltaDivisionFirstBaseIdeal (p := p) (C d) x
  let T := DeltaAdjoinDivision DU (C d) x
  let K := deltaAdjoinDivisionResidueIdeal DU (C d) x
  let L := RelativeFreeDeltaRing (R := U) S
  have hpU : Function.Injective (fun z : U => (p : U) * z) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hp).of_flat (S := U)
  have hpL : Function.Injective (fun z : L => (p : L) * z) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular U (p : U) from hpU).of_flat (S := L)
  have hg : Function.Injective (WittVector.ghostMap : WittVector p L → ℕ → L) :=
    witt_ghostMap_injective_of_mul_prime_injective p L hpL
  let v : Uˣ := Units.map C.toMonoidHom u
  have hv : (v : U) = DU.delta (C d) := by
    change C (u : A) = DU.delta (C d)
    rw [hu, relativeFreeDeltaStructure_delta_C]
  obtain ⟨e, _, he, _⟩ := exists_deltaDivision_freeVariable_equiv (S := S) D d
  have hd : e.toRingHom (deltaAdjoinDivisionMap DU (C d) x (C d)) = C d :=
    (RingHom.congr_fun he (C d)).trans (deltaDivisionSourceMap_C D d d)
  have hK : K.map e.toRingHom = I := by
    change (Ideal.span {(p : T), deltaAdjoinDivisionMap DU (C d) x (C d)}).map e.toRingHom = I
    rw [Ideal.map_span, Set.image_pair, map_natCast, hd]
  let eQ := Ideal.quotientEquiv K I e hK.symm
  let bT : U ⧸ J →+* T ⧸ K := deltaAdjoinDivisionResidueBaseMap DU hpU hpL hg (C d) x v hv
  let b := eQ.toRingHom.comp bT
  refine ⟨b, ?_, ?_⟩
  · intro z
    change eQ (bT (Ideal.Quotient.mk J z)) = _
    rw [deltaAdjoinDivisionResidueBaseMap_mk]
    change Ideal.Quotient.mk I (e (deltaAdjoinDivisionMap DU (C d) x z)) = _
    exact congrArg (Ideal.Quotient.mk I) (RingHom.congr_fun he z)
  · let := deltaAdjoinDivisionResidueBaseAlgebra DU hpU hpL hg (C d) x v hv
    let := b.toAlgebra
    let eA : (T ⧸ K) ≃ₐ[U ⧸ J] (U ⧸ I) := AlgEquiv.ofRingEquiv (f := eQ) (fun _ => rfl)
    let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat DU hpU hpL hg (C d) x v hv
    exact Module.FaithfullyFlat.of_linearEquiv _ _ eA.symm.toLinearEquiv

end SerrePositivity.BhattScholze
