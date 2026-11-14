module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation

/-!
# 自由変数の envelope の完備底変換

## 概要
完備自由 δ 環は prism の任意の射による完備底変換と可換。

## 方針
完備テンソル積と完備自由環を、係数射と初期変数の指定による普遍性で比較する。

## 規約
BS 著者版 Proposition 3.13 (2) と Example 3.14 の変数の場合。

## 使われ方
変数に沿う envelope の完備底変換。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open DerivedCompletion
open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime] {A A' : Type u} [CommRing A] [CommRing A']
variable (P : OrientedPrism p A) (P' : OrientedPrism p A')
variable (f : OrientedPrism.Hom P P') (S : Type u)

local notation "B" => completedFreeDelta P S
local notation "B'" => completedFreeDelta P' S
local notation "b" => completedFreeDeltaBase P S
local notation "b'" => completedFreeDeltaBase P' S
local notation "DB" => completedFreeDeltaStructure P S
local notation "DB'" => completedFreeDeltaStructure P' S
local notation "X" => completedFreeDeltaVariable P S
local notation "X'" => completedFreeDeltaVariable P' S

private theorem complete_mul_generator_image {T : Type u} [CommRing T]
    (a : A' →+* T)
    (h : IsModuleComplete T (a P'.generator) (ModuleCat.of T T)) :
    IsModuleComplete T (a (f.toRingHom P.generator)) (ModuleCat.of T T) := by
  obtain ⟨u, hu⟩ := f.map_generator_unit_mul
  rw [hu, map_mul]
  exact isModuleComplete_mul_right T _ _ _ h

/-- 概要：完備自由 δ 環の完備底変換の比較。
方針：両方向をそれぞれの普遍性で構成し、係数と初期変数上で逆になることを確かめる。
規約：BS 著者版 Proposition 3.13 (2) の変数模型。二つの係数脚と変数を追跡する。
使われ方：変数の置換で作る envelope の底変換。 -/
theorem exists_completedFreeDelta_baseChange_equiv :
    letI := f.toRingHom.toAlgebra
    letI := (b).toAlgebra
    let H := PrismCompletedTensor (A := A) (C := B) P'
    let D := prismCompletedTensorDelta P' P.deltaStructure DB f.map_delta
      (completedFreeDeltaBase_isDeltaHom P S)
    ∃ e : H ≃+* B', D.IsDeltaHom DB' e.toRingHom ∧
      e.toRingHom.comp (prismCompletedTensorLeft P') = b' ∧
      ∀ s : S, e (prismCompletedTensorRight P' (X s)) = X' s := by
  let := f.toRingHom.toAlgebra
  let := (b).toAlgebra
  let H := PrismCompletedTensor (A := A) (C := B) P'
  let L : A' →+* H := prismCompletedTensorLeft P'
  let R : B →+* H := prismCompletedTensorRight P'
  let D := prismCompletedTensorDelta P' P.deltaStructure DB f.map_delta
    (completedFreeDeltaBase_isDeltaHom P S)
  have hL : P'.deltaStructure.IsDeltaHom D L :=
    prismCompletedTensorLeft_isDeltaHom P' P.deltaStructure DB f.map_delta
      (completedFreeDeltaBase_isDeltaHom P S)
  have hR : (DB).IsDeltaHom D R :=
    prismCompletedTensorRight_isDeltaHom P' P.deltaStructure DB f.map_delta
      (completedFreeDeltaBase_isDeltaHom P S)
  have hw : L.comp f.toRingHom = R.comp b := prismCompletedTensor_square P'
  have hpH : IsModuleComplete H (p : H) (ModuleCat.of H H) :=
    prismCompletedTensor_complete_p P'
  have hdH : IsModuleComplete H (L P'.generator) (ModuleCat.of H H) :=
    prismCompletedTensor_complete_generator P'
  have hp' := completedFreeDelta_complete_p P' S
  have hd' := completedFreeDelta_complete_generator P' S
  have hb' := completedFreeDeltaBase_isDeltaHom P' S
  have hfb' := hb'.comp f.map_delta
  have hfd' := complete_mul_generator_image P P' f b' hd'
  obtain ⟨g, hg, _⟩ := existsUnique_completedFreeDeltaHom P S DB' ((b').comp f.toRingHom)
    hfb' hp' hfd' X'
  obtain ⟨k, hk, _⟩ := existsUnique_prismCompletedTensorHom P' P.deltaStructure DB f.map_delta
    (completedFreeDeltaBase_isDeltaHom P S) DB' b' g hb' hg.1 hg.2.1.symm hp' hd'
  obtain ⟨t, ht, _⟩ := existsUnique_completedFreeDeltaHom P' S D L hL hpH hdH (R ∘ X)
  have hkR (x : B) : k (R x) = g x := DFunLike.congr_fun hk.2.2 x
  have hkt : k.comp t = RingHom.id B' := by
    apply completedFreeDeltaHom_ext P' S DB' b' hb' hp' hd' (hk.1.comp ht.1)
      (DB').isDeltaHom_id
    · rw [RingHom.comp_assoc, ht.2.1, hk.2.1]
    · exact RingHom.id_comp _
    · intro s
      change k (t (X' s)) = X' s
      rw [ht.2.2 s, Function.comp_apply, hkR, hg.2.2 s]
  have htkR : t.comp g = R := by
    have hfdH := complete_mul_generator_image P P' f L hdH
    apply completedFreeDeltaHom_ext P S D (L.comp f.toRingHom) (hL.comp f.map_delta) hpH hfdH
      (ht.1.comp hg.1) hR
    · rw [RingHom.comp_assoc, hg.2.1, ← RingHom.comp_assoc, ht.2.1]
    · exact hw.symm
    · intro s
      change t (g (X s)) = R (X s)
      rw [hg.2.2 s, ht.2.2 s]
      rfl
  have htk : t.comp k = RingHom.id H := by
    apply prismCompletedTensorHom_ext P' P.deltaStructure DB f.map_delta
      (completedFreeDeltaBase_isDeltaHom P S) D (ht.1.comp hk.1) D.isDeltaHom_id
    · change (t.comp k).comp L = (RingHom.id H).comp L
      rw [RingHom.comp_assoc, hk.2.1, ht.2.1, RingHom.id_comp]
    · change (t.comp k).comp R = (RingHom.id H).comp R
      rw [RingHom.comp_assoc, hk.2.2, htkR, RingHom.id_comp]
    · exact hpH
    · exact hdH
  exact ⟨RingEquiv.ofRingHom k t hkt htk, hk.1, hk.2.1,
    fun s ↦ (hkR (X s)).trans (hg.2.2 s)⟩

/-- 概要：変数に沿う prismatic envelope は完備底変換と可換。
方針：自由変数模型で標的の正則性と有界性を示す。持ち上げは元の envelope と完備テンソル積の普遍性から得る。
規約：BS 著者版 Proposition 3.13 (2) の変数の場合。拡大イデアルは右脚による像。
使われ方：変数模型による affine Čech–Alexander 構成の底変換。 -/
theorem prismaticEnvelope_completedBaseChange_of_variables
    (hP : IsBoundedPrism P) (hP' : IsBoundedPrism P') (Z : Set S)
    {C : Type u} [CommRing C] (Q : OrientedPrism p C) (η : B →+* C)
    (hJ : b P.generator ∈ variableIdeal P S Z)
    (h : IsPrismaticEnvelope P DB b (completedFreeDeltaBase_isDeltaHom P S)
      (variableIdeal P S Z) hJ Q η) :
    letI := f.toRingHom.toAlgebra
    letI := (b).toAlgebra
    letI := (η.comp b).toAlgebra
    let H := PrismCompletedTensor (A := A) (C := B) P'
    let K := PrismCompletedTensor (A := A) (C := C) P'
    let l : A' →+* H := prismCompletedTensorLeft P'
    let r : B →+* H := prismCompletedTensorRight P'
    let lC : A' →+* K := prismCompletedTensorLeft P'
    let rC : C →+* K := prismCompletedTensorRight P'
    let J := (variableIdeal P S Z).map r
    ∃ (D : DeltaStructure p H) (Q' : OrientedPrism p K) (η' : H →+* K)
      (hl : P'.deltaStructure.IsDeltaHom D l) (hd : l P'.generator ∈ J),
      (DB).IsDeltaHom D r ∧ Q.deltaStructure.IsDeltaHom Q'.deltaStructure rC ∧
      η'.comp r = rC.comp η ∧ η'.comp l = lC ∧ IsBoundedPrism Q' ∧
      IsPrismaticEnvelope P' D l hl J hd Q' η' := by
  let := f.toRingHom.toAlgebra
  let := (b).toAlgebra
  let := (η.comp b).toAlgebra
  let H := PrismCompletedTensor (A := A) (C := B) P'
  let K := PrismCompletedTensor (A := A) (C := C) P'
  let l : A' →+* H := prismCompletedTensorLeft P'
  let r : B →+* H := prismCompletedTensorRight P'
  let lC : A' →+* K := prismCompletedTensorLeft P'
  let rC : C →+* K := prismCompletedTensorRight P'
  let J := (variableIdeal P S Z).map r
  let hb := completedFreeDeltaBase_isDeltaHom P S
  let hbC := h.isDeltaHom.comp hb
  let D := prismCompletedTensorDelta P' P.deltaStructure DB f.map_delta hb
  let F := prismCompletedTensorDelta P' P.deltaStructure Q.deltaStructure f.map_delta hbC
  have hl : P'.deltaStructure.IsDeltaHom D l :=
    prismCompletedTensorLeft_isDeltaHom P' P.deltaStructure DB f.map_delta hb
  have hr : (DB).IsDeltaHom D r :=
    prismCompletedTensorRight_isDeltaHom P' P.deltaStructure DB f.map_delta hb
  have hlC : P'.deltaStructure.IsDeltaHom F lC :=
    prismCompletedTensorLeft_isDeltaHom P' P.deltaStructure Q.deltaStructure f.map_delta hbC
  have hrC : Q.deltaStructure.IsDeltaHom F rC :=
    prismCompletedTensorRight_isDeltaHom P' P.deltaStructure Q.deltaStructure f.map_delta hbC
  have hsq : l.comp f.toRingHom = r.comp b := prismCompletedTensor_square P'
  have hsqC : lC.comp f.toRingHom = rC.comp (η.comp b) := prismCompletedTensor_square P'
  obtain ⟨a, ha⟩ := f.map_generator_unit_mul
  have span_image {T : Type u} [CommRing T] (g : A' →+* T) :
      Ideal.span {g (f.toRingHom P.generator)} = Ideal.span {g P'.generator} := by
    rw [ha, map_mul, Ideal.span_singleton_mul_right_unit (a.isUnit.map g)]
  have hd : l P'.generator ∈ J := by
    have hm : l (f.toRingHom P.generator) ∈ J := by
      rw [show l (f.toRingHom P.generator) = r (b P.generator) from RingHom.congr_fun hsq _]
      exact Ideal.mem_map_of_mem r hJ
    have hs : Ideal.span {l (f.toRingHom P.generator)} ≤ J :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    rw [span_image l] at hs
    exact hs (Ideal.subset_span rfl)
  obtain ⟨e₀, he₀, he₀η⟩ := h.unique P
    (isPrismaticEnvelope_variableSubstitution P S Z (completedFreeDelta_generator_regular P hP S))
  have he₀b : e₀.toRingHom.comp (η.comp b) = b := by
    rw [← RingHom.comp_assoc, he₀η, variableEnvelopeSubstitution_base]
  obtain ⟨e₁, _, he₁l, _⟩ := exists_prismCompletedTensor_right_equiv P' P.deltaStructure
    Q.deltaStructure f.map_delta hbC DB hb e₀ he₀ he₀b
  obtain ⟨e₂, _, he₂l, _⟩ := exists_completedFreeDelta_baseChange_equiv P P' f S
  let e : K ≃+* B' := e₁.trans e₂
  have hel : e.toRingHom.comp lC = b' := by
    change (e₂.toRingHom.comp e₁.toRingHom).comp lC = b'
    rw [RingHom.comp_assoc, he₁l, he₂l]
  let dK := lC P'.generator
  have hed : e dK = b' P'.generator := RingHom.congr_fun hel P'.generator
  have hreg : Function.Injective (dK * ·) := by
    intro x y hxy
    apply e.injective
    apply completedFreeDelta_generator_regular P' hP' S
    simpa only [map_mul, hed] using congrArg e hxy
  let hpK : IsModuleComplete K (p : K) (ModuleCat.of K K) := prismCompletedTensor_complete_p P'
  let hdK : IsModuleComplete K dK (ModuleCat.of K K) :=
    prismCompletedTensor_complete_generator P'
  let Q' := OrientedPrism.ofDistinguished F dK (hlC.map_isDistinguished P'.isDistinguished_generator)
    hreg hpK hdK
  have hQ' : IsBoundedPrism Q' := by
    have hm : Ideal.span {b' P'.generator} = (Ideal.span {dK}).map e.toRingHom := by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {b' P'.generator} = Ideal.span {e dK}
      rw [hed]
    let eq := Ideal.quotientEquiv _ _ e hm
    obtain ⟨N, hN⟩ := completedFreeDelta_residue_bounded P' hP' S
    refine ⟨N, fun n x hx ↦ eq.injective ?_⟩
    rw [map_zero, map_mul, map_pow, map_natCast]
    apply hN n
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eq hx
  have hsqC' : lC.comp f.toRingHom = (rC.comp η).comp b := hsqC.trans
    (RingHom.comp_assoc b η rC).symm
  obtain ⟨η', hη', _⟩ := existsUnique_prismCompletedTensorHom P' P.deltaStructure DB
    f.map_delta hb F lC (rC.comp η) hlC (hrC.comp h.isDeltaHom)
    hsqC' hpK hdK
  have hηl : η'.comp l = lC := hη'.2.1
  have hηr : η'.comp r = rC.comp η := hη'.2.2
  refine ⟨D, Q', η', hl, hd, hr, hrC, hηr, hηl, hQ', ?_⟩
  refine ⟨hη'.1, ?_, ?_, ?_, ?_⟩
  · rw [hηl, OrientedPrism.ideal, Ideal.span_le]
    exact Set.singleton_subset_iff.mpr (Ideal.subset_span rfl)
  · change Ideal.span {dK} = Ideal.span {η' (l P'.generator)}
    rw [show η' (l P'.generator) = dK from RingHom.congr_fun hηl _]
  · change J.map η' ≤ Ideal.span {dK}
    rw [Ideal.map_map, hηr, ← Ideal.map_map]
    refine (Ideal.map_mono h.map_le).trans ?_
    rw [h.ideal_eq, Ideal.map_span, Set.image_singleton]
    change Ideal.span {(rC.comp (η.comp b)) P.generator} ≤ Ideal.span {dK}
    rw [← hsqC, RingHom.comp_apply, span_image lC]
  · intro T _ QT g hg hgbase hgJ
    let i : OrientedPrism.Hom P' QT := ⟨g.comp l, hg.comp hl, hgbase⟩
    have hgr : (g.comp r).comp b = i.toRingHom.comp f.toRingHom := by
      change (g.comp r).comp b = (g.comp l).comp f.toRingHom
      rw [RingHom.comp_assoc b r g, ← hsq, RingHom.comp_assoc f.toRingHom l g]
    have hgrbase : P.ideal ≤ QT.ideal.comap ((g.comp r).comp b) := by
      rw [hgr]
      exact (i.comp f).ideal_le
    have hgrJ : (variableIdeal P S Z).map (g.comp r) ≤ QT.ideal := by
      rw [← Ideal.map_map]
      exact hgJ
    obtain ⟨k, hk, hku⟩ := h.lift QT (g.comp r) (hg.comp hr) hgrbase hgrJ
    have hw : i.toRingHom.comp f.toRingHom = k.comp (η.comp b) := by
      rw [← hgr]
      calc
        (g.comp r).comp b = (k.comp η).comp b := congrArg (fun t : B →+* T ↦ t.comp b) hk.2.symm
        _ = k.comp (η.comp b) := RingHom.comp_assoc b η k
    obtain ⟨j, hj, _⟩ := existsUnique_prismCompletedTensorHom P' P.deltaStructure
      Q.deltaStructure f.map_delta hbC QT.deltaStructure i.toRingHom k i.map_delta hk.1
      hw QT.complete_p i.isModuleComplete_map_generator
    have hjη : j.comp η' = g := by
      apply prismCompletedTensorHom_ext P' P.deltaStructure DB f.map_delta hb QT.deltaStructure
        (hj.1.comp hη'.1) hg
      · change (j.comp η').comp l = g.comp l
        rw [RingHom.comp_assoc, hηl, hj.2.1]
      · change (j.comp η').comp r = g.comp r
        rw [RingHom.comp_assoc, hηr, ← RingHom.comp_assoc, hj.2.2, hk.2]
      · exact QT.complete_p
      · exact i.isModuleComplete_map_generator
    refine ⟨j, ⟨hj.1, hjη⟩, fun j' hj' ↦ ?_⟩
    apply prismCompletedTensorHom_ext P' P.deltaStructure Q.deltaStructure f.map_delta hbC
      QT.deltaStructure hj'.1 hj.1
    · change j'.comp lC = j.comp lC
      rw [hj.2.1, ← hηl, ← RingHom.comp_assoc, hj'.2]
    · change j'.comp rC = j.comp rC
      rw [hj.2.2]
      apply hku
      refine ⟨hj'.1.comp hrC, ?_⟩
      rw [RingHom.comp_assoc, ← hηr, ← RingHom.comp_assoc, hj'.2]
    · exact QT.complete_p
    · change IsModuleComplete T (j dK) (ModuleCat.of T T)
      rw [show j dK = i.toRingHom P'.generator from RingHom.congr_fun hj.2.1 _]
      exact i.isModuleComplete_map_generator

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 3.13" (partial := special) "向き付き・B＝完備自由 δ 環・J＝(d, 変数) の場合に存在と完全平坦性 (1)。底変換 (2) は変数の場合が本体（prismaticEnvelope_completedBaseChange_of_variables）。一般の正則な B, J は未 ／ 11-10 更新 ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.prismaticEnvelope_completedBaseChange_of_variables
