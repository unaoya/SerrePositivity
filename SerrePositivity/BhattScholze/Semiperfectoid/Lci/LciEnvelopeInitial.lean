module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelope

/-!
# 有界な包絡の始性

## 概要
基底環のイデアルに対する有界な包絡は、その商の prismatic site の始対象になる。

## 方針
商からの剰余脚を、イデアルが向きのイデアルに入る条件として読み替える。

## 規約
BS 著者版 Example 7.9 の包絡側。環側の圏と濃度上限を使う。

## 使われ方
有界な lci 包絡を site の始対象として読む。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable {J : Ideal A} (hJ : P.ideal ≤ J)
variable {η : A →+* B}

local notation "hgen" => (hJ (Ideal.subset_span (Set.mem_singleton P.generator)))

/-- 概要：包絡が有界で濃度上限を満たせば、その台環で site の始対象を作れる。
方針：イデアルを送る条件を商の剰余脚に移し、包絡の一意な持ち上げを使う。
規約：BS 著者版 Example 7.9 の古典的な始性。
使われ方：lci 商の包絡による始対象の構成。 -/
theorem IsPrismaticEnvelope.exists_initial_of_base_quotient
    (hE : IsPrismaticEnvelope P P.deltaStructure (RingHom.id A)
      P.deltaStructure.isDeltaHom_id J hgen Q η)
    (hb : IsBoundedPrism Q) {κ : Cardinal.{u}} (hκ : Cardinal.mk B ≤ κ) :
    letI := (Ideal.Quotient.factor hJ).toAlgebra
    ∃ Y : PrismOver P (A ⧸ J) κ, Nonempty (IsInitial Y) := by
  let := (Ideal.Quotient.factor hJ).toAlgebra
  let b : OrientedPrism.Hom P Q := ⟨η, hE.isDeltaHom, by simpa using hE.base_hom⟩
  let s : (A ⧸ J) →+* B ⧸ Q.ideal :=
    Ideal.quotientMap Q.ideal η (Ideal.map_le_iff_le_comap.mp hE.map_le)
  let Y : PrismOver P (A ⧸ J) κ :=
    { B := B
      Q := Q
      bounded := hb
      toHom := b
      sec := s
      sec_comp := by
        apply Ideal.Quotient.ringHom_ext
        rfl
      small := hκ }
  have lift (X : PrismOver P (A ⧸ J) κ) : ∃! v : B →+* X.B,
      Q.deltaStructure.IsDeltaHom X.Q.deltaStructure v ∧ v.comp η = X.toHom.toRingHom := by
    have hs (a : A) :
        Ideal.Quotient.mk X.Q.ideal (X.toHom.toRingHom a) = X.sec (Ideal.Quotient.mk J a) :=
      (RingHom.congr_fun X.sec_comp (Ideal.Quotient.mk P.ideal a)).symm
    apply hE.lift X.Q X.toHom.toRingHom X.toHom.map_delta (by simpa using X.toHom.ideal_le)
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change X.toHom.toRingHom a ∈ X.Q.ideal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hs, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have siteLift (X : PrismOver P (A ⧸ J) κ) (v : B →+* X.B)
      (hv : Q.deltaStructure.IsDeltaHom X.Q.deltaStructure v)
      (hvη : v.comp η = X.toHom.toRingHom) : ∃ a : Y ⟶ X, a.toHom.toRingHom = v := by
    let w : OrientedPrism.Hom Q X.Q := ⟨v, hv, by
      rw [hE.ideal_eq, Ideal.span_le]
      apply Set.singleton_subset_iff.mpr
      change (v.comp η) P.generator ∈ X.Q.ideal
      rw [hvη]
      exact X.toHom.map_generator_mem⟩
    let a : Y ⟶ X := ⟨w, OrientedPrism.Hom.ext hvη, by
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro z
      change Ideal.Quotient.mk X.Q.ideal ((v.comp η) z) = X.sec (Ideal.Quotient.mk J z)
      rw [hvη]
      exact (RingHom.congr_fun X.sec_comp (Ideal.Quotient.mk P.ideal z)).symm⟩
    exact ⟨a, rfl⟩
  let a (X : PrismOver P (A ⧸ J) κ) : Y ⟶ X :=
    (siteLift X (lift X).choose (lift X).choose_spec.1.1 (lift X).choose_spec.1.2).choose
  refine ⟨Y, ⟨IsInitial.ofUniqueHom a ?_⟩⟩
  intro X m
  apply PrismOver.Hom.ext
  apply OrientedPrism.Hom.ext
  change m.toHom.toRingHom = (a X).toHom.toRingHom
  rw [(siteLift X (lift X).choose (lift X).choose_spec.1.1 (lift X).choose_spec.1.2).choose_spec]
  exact (lift X).choose_spec.2 _ ⟨m.toHom.map_delta,
    congrArg OrientedPrism.Hom.toRingHom m.comm_base⟩

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 7.9" (partial := component) "BS-W15 K5（11-11）：envelope の側は本体（R の有界性を仮定する原典の形、D76。結論は有界な prism）。p 反転の議論 G-A3-7 の古典的な入力（余法加群、分冪の像の稠密性）も本体。Δ_R/A との同一視と HT 比較の適用は drafts の A3/LciAndQuasiregular"] _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.exists_initial_of_base_quotient
