module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.Envelope
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.BhattScholze.Semiperfectoid.Discrete.DiscretePrism
import SerrePositivity.BhattScholze.Prism.Basic.Rigidity

/-!
# 完備テンソル積による lci 包絡の普遍性

## 概要
分類射に沿う完備テンソル積で基底の生成元が正則なら、延長したイデアルの包絡になる。

## 方針
元の包絡の持ち上げを完備テンソル積の二脚に貼り合わせる。

## 規約
BS 著者版 Example 7.9 の包絡側。完備化の H⁰ に対する正則性を入力とする。

## 使われ方
普遍自由変数の包絡を、指定の関係列に特殊化する。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime]
variable {A₀ A U E : Type u} [CommRing A₀] [CommRing A] [CommRing U] [CommRing E]
variable (P₀ : OrientedPrism p A₀) (P : OrientedPrism p A)
variable (DU : DeltaStructure p U) (ι : A₀ →+* U) (hι : P₀.deltaStructure.IsDeltaHom DU ι)
variable (J : Ideal U) (hJ : ι P₀.generator ∈ J)
variable (Q : OrientedPrism p E) (η : U →+* E) (hE : IsPrismaticEnvelope P₀ DU ι hι J hJ Q η)
variable (c : U →+* A) (hc : DU.IsDeltaHom P.deltaStructure c)

include hE hc in
/-- 概要：分類射に沿う完備テンソル積は、生成元の像が正則なら延長イデアルの包絡。
方針：標的への基底脚を元の包絡の普遍性に入れ、両脚を完備テンソル積から一意に延長する。
規約：BS 著者版 Example 7.9 の古典的な普遍性。台環の正則性は別途検証する。
使われ方：自由変数で得た包絡を有限の関係列へ特殊化する。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_envelope_of_classified_ideal_of_regular (g : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P₀ P)
    (hg : c.comp ι = g.toRingHom)
    (hd : g.toRingHom P₀.generator = P.generator)
    (hreg : letI := c.toAlgebra; letI := η.toAlgebra
      IsRegular ((_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft (A := U) (C := E) P) P.generator)) :
    letI := c.toAlgebra; letI := η.toAlgebra
    let H := _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) (C := E) P
    let l : A →+* H := _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft P
    ∃ Q' : _root_.SerrePositivity.BhattScholze.OrientedPrism p H, Q'.generator = l P.generator ∧
      _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope P P.deltaStructure (RingHom.id A) P.deltaStructure.isDeltaHom_id
        (J.map c) (by
          change P.generator ∈ J.map c
          rw [← hd, ← show c (ι P₀.generator) = _ from RingHom.congr_fun hg P₀.generator]
          exact Ideal.mem_map_of_mem c hJ) Q' l := by
  let := c.toAlgebra
  let := η.toAlgebra
  let H := _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) (C := E) P
  let l : A →+* H := _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft P
  let r : E →+* H := _root_.SerrePositivity.BhattScholze.prismCompletedTensorRight P
  let D := _root_.SerrePositivity.BhattScholze.prismCompletedTensorDelta P DU Q.deltaStructure hc hE.isDeltaHom
  have hl := _root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft_isDeltaHom P DU Q.deltaStructure hc hE.isDeltaHom
  have hr := _root_.SerrePositivity.BhattScholze.prismCompletedTensorRight_isDeltaHom P DU Q.deltaStructure hc hE.isDeltaHom
  have hw : l.comp c = r.comp η := _root_.SerrePositivity.BhattScholze.prismCompletedTensor_square P
  let Q' := P.ofDiscreteDelta D l hl hreg
    (_root_.SerrePositivity.BhattScholze.prismCompletedTensor_complete_p P) (_root_.SerrePositivity.BhattScholze.prismCompletedTensor_complete_generator P)
  have hbase : P.ideal ≤ Q'.ideal.comap l :=
    (P.toDiscreteDelta D l hl hreg
      (_root_.SerrePositivity.BhattScholze.prismCompletedTensor_complete_p P) (_root_.SerrePositivity.BhattScholze.prismCompletedTensor_complete_generator P)).ideal_le
  have hd' : c (ι P₀.generator) = P.generator := (RingHom.congr_fun hg _).trans hd
  have hmapE : Q.ideal.map r ≤ Q'.ideal := by
    rw [hE.ideal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le]
    apply Set.singleton_subset_iff.mpr
    have h : r (η (ι P₀.generator)) = l P.generator :=
      (RingHom.congr_fun hw _).symm.trans (congrArg l hd')
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton _)
  refine ⟨Q', rfl, hl, hbase, rfl, ?_, ?_⟩
  · rw [Ideal.map_map, hw, ← Ideal.map_map]
    exact (Ideal.map_mono hE.map_le).trans hmapE
  · intro T _ QT v hv hbaseT hJT
    have hvBase : P.ideal ≤ QT.ideal.comap v := by simpa using hbaseT
    let vP : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P QT := ⟨v, hv, hvBase⟩
    have hb₀ : P₀.ideal ≤ QT.ideal.comap ((v.comp c).comp ι) := by
      rw [RingHom.comp_assoc, hg]
      exact (vP.comp g).ideal_le
    have hJ₀ : J.map (v.comp c) ≤ QT.ideal := by
      rw [← Ideal.map_map]
      exact hJT
    obtain ⟨k, hk, hkuniq⟩ := hE.lift QT (v.comp c) (hv.comp hc) hb₀ hJ₀
    obtain ⟨t, ht, htuniq⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_prismCompletedTensorHom
      P DU Q.deltaStructure hc hE.isDeltaHom QT.deltaStructure
      v k hv hk.1 hk.2.symm QT.complete_p vP.isModuleComplete_map_generator
    refine ⟨t, ⟨ht.1, ht.2.1⟩, fun s hs ↦ htuniq s ⟨hs.1, hs.2, ?_⟩⟩
    apply hkuniq
    refine ⟨hs.1.comp hr, ?_⟩
    change (s.comp r).comp η = v.comp c
    rw [RingHom.comp_assoc, ← hw, ← RingHom.comp_assoc, hs.2]

end SerrePositivity.BhattScholze.Prismatic
