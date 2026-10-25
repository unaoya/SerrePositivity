module

public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectSourceAdicRigidity
public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismAdicComplete
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-!
# André A1-a：完全な源から一般有界 prism への射の一意性

## 概要

完全 δ 環から有界 prism の台環への環射は、prism 商への合成で決まる。
完全 prism からの prism 射も商射で決まる。BS Lemma 4.8（著者版 pp.38–39）の一意性。

## 方針

完全な源で a=b^p+p*δ(b) を供給し、標的の (p,d) 分離性と幾何和による剛性を使う。
原典の変形理論・逆極限による δ 判定とは異なる、差のイデアル冪による直接証明。

## 規約

標的の完全性・p 正則性は不要。持上げの存在はまだ結論しない。

## 使われ方

BS Rem 7.15（著者版 p.62）の基底射の選択の一意性と入力圏の比較に使う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 概要：完全 δ 源から有界 prism への環射は、標準 prism 商への合成で決まる。
方針：完全 Frobenius による p 冪近似と標的の (p,d) 分離性で差を全冪に入れる。
規約：射の δ 保存性すらこの剛性には不要。標的の p 正則性を要求しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の一般有界標的での一意性。 -/
theorem ringHom_ext_to_boundedPrism_of_perfect_source
    (D : DeltaStructure p A) (hD : D.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (F G : A →+* B)
    (hFG : (Ideal.Quotient.mk Q.ideal).comp F = (Ideal.Quotient.mk Q.ideal).comp G) :
    F = G := by
  let Jp : Ideal B := Ideal.span {(p : B), Q.generator}
  let := boundedPrism_pair_isAdicComplete Q hB
  have hA : ∀ a : A, ∃ b c : A, a = b ^ p + (p : A) * c := by
    intro a
    obtain ⟨b, hb⟩ := hD.2 a
    exact ⟨b, D.delta b, hb.symm.trans (D.frobeniusLift_apply b)⟩
  apply ringHom_ext_of_pow_add_natCast_mul p hA Jp (Ideal.subset_span (by simp)) F G
  have hQI : Q.ideal ≤ Jp := by
    change Ideal.span {Q.generator} ≤ Jp
    apply Ideal.span_le.mpr
    intro x hx
    exact Ideal.subset_span (Set.mem_insert_of_mem _ hx)
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk Jp (F a) = Ideal.Quotient.mk Jp (G a)
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hQI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, sub_eq_zero]
  exact RingHom.congr_fun hFG a

/-- 概要：完全 prism から有界 prism への射は、その誘導商射で一意に決まる。
方針：商射の合成公式で環射の剛性へ帰着する。
規約：標的を完全 prism に制限しない。持上げの存在は主張しない。
使われ方：BS Lemma 4.8（著者版 pp.38–39）の基底持上げの一意性。 -/
theorem perfectPrismHom_ext_to_bounded_target
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (F G : OrientedPrism.Hom W Q) (hFG : F.quotientMap = G.quotientMap) : F = G := by
  apply OrientedPrism.Hom.ext
  apply ringHom_ext_to_boundedPrism_of_perfect_source W.deltaStructure hW Q hB
  rw [← OrientedPrism.Hom.quotientMap_comp_mk, ← OrientedPrism.Hom.quotientMap_comp_mk, hFG]

end SerrePositivity.BhattScholze.Andre
