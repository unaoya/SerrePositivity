module

public import SerrePositivity.BhattScholze.Andre.Remark715.BoundedPrismAdicComplete
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-!
# André E1・E2：有界試験 prism への基底射の生成元の単元係数

## 概要

源の生成元が distinguished なら、有界試験 prism への prism 射は生成元を
一意な単元倍へ送る。BS Rem 7.15（著者版 p.62）の一般の基底射への対応。

## 方針

生成元の像の distinguished 性と (p,d) 完備性による Jacobson 条件から係数の単元性を得る。
原典とは異なる有界ねじれからの共通古典的完備性を使う証明。

## 規約

標的の完全性・p 正則性は不要。源には指定生成元の distinguished 性を明示する。

## 使われ方

実完備化の普遍射から、生成元の像が厳密に一致するという補助条件を除く。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (F : OrientedPrism.Hom P Q)
variable (hP : P.deltaStructure.IsDistinguished P.generator)
variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hP hB in
/-- 概要：有界試験 prism への射の生成元の像には一意な単元係数がある。
方針：生成元の像を d*r と書き、distinguished 積の係数の単元性を使う。
規約：標的の p 正則性や完全性を前提に残さない。
使われ方：BS Rem 7.15（著者版 p.62）の一般の基底 prism 射の扱い。 -/
theorem existsUnique_boundedPrismHom_generator_unit :
    ∃! z : Bˣ, F.toRingHom P.generator = Q.generator * z := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp F.map_generator_mem
  have hdist := F.map_delta.map_isDistinguished hP
  rw [hr] at hdist
  let := boundedPrism_pair_isAdicComplete Q hB
  have hru : IsUnit r :=
    (Q.deltaStructure.isDistinguished_factor Q.generator r hdist
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B), Q.generator})
        (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B), Q.generator})
        (Ideal.subset_span (by simp)))).2
  obtain ⟨z, hz⟩ := hru
  refine ⟨z, by simpa only [hz] using hr, ?_⟩
  intro w hw
  apply Units.ext
  apply Q.generator_regular
  change Q.generator * (w : B) = Q.generator * (z : B)
  exact hw.symm.trans (by simpa only [hz] using hr)

include hP hB in
/-- 概要：基底生成元の像が生成する主イデアルは標的の prism イデアル全体。
方針：生成元の単元係数と主イデアルの単元倍不変性を使う。
規約：選択した orientation 自体の一致は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分子の可除性と完備性の移送。 -/
theorem boundedPrismHom_generator_span :
    Ideal.span {F.toRingHom P.generator} = Q.ideal := by
  obtain ⟨z, hz, _⟩ := existsUnique_boundedPrismHom_generator_unit F hP hB
  rw [hz]
  exact Ideal.span_singleton_mul_right_unit z.isUnit Q.generator

include hP hB in
/-- 概要：有界試験 prism への基底生成元の像は非零因子。
方針：標的生成元と一意な単元係数の二つの乗法写像を消去する。
規約：標的の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の raw 除算包の試験環への一意普遍射。 -/
theorem boundedPrismHom_generator_regular :
    Function.Injective (fun x : B => F.toRingHom P.generator * x) := by
  obtain ⟨z, hz, _⟩ := existsUnique_boundedPrismHom_generator_unit F hP hB
  intro x y hxy
  change F.toRingHom P.generator * x = F.toRingHom P.generator * y at hxy
  rw [hz, mul_assoc, mul_assoc] at hxy
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp z.isUnit).1 (Q.generator_regular hxy)

include hP hB in
/-- 概要：有界試験 prism は基底生成元の像に沿って導来完備。
方針：主イデアルの一致で標的の古典的生成元完備性を移し、導来完備性へ戻す。
規約：生成元を取り直した試験 prism を新設しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実完備化からの比較射。 -/
theorem boundedPrismHom_generator_complete :
    IsModuleComplete B (F.toRingHom P.generator) (ModuleCat.of B B) := by
  let : IsAdicComplete (Ideal.span {F.toRingHom P.generator}) B := by
    rw [boundedPrismHom_generator_span F hP hB]
    exact Q.isAdicComplete_generator
  exact isModuleComplete_of_isAdicComplete B (F.toRingHom P.generator) (ModuleCat.of B B)

include hP hB in
/-- 概要：有界試験 prism への射は prism イデアルを標的のイデアル全体へ写す。
方針：主イデアルの像を生成元の像で計算する。
規約：一般のイデアル保存 prism 射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の基底 prism 上の普遍性。 -/
theorem boundedPrismHom_map_ideal_eq : P.ideal.map F.toRingHom = Q.ideal := by
  rw [OrientedPrism.ideal, Ideal.map_span, Set.image_singleton]
  exact boundedPrismHom_generator_span F hP hB

end SerrePositivity.BhattScholze.Andre
