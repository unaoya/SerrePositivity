module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionAlgebraUniversal
open SerrePositivity
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R S : Type u} [CommRing R] [CommRing S] (p : ℕ)
/-- ## 概要
p 進完備な環 S への任意の環射 R→S を、R の通常 p 進完備化からの環射へ延長する。
BS Thm 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
R の作用を元の環射から定め、p 主イデアルの写像を計算して、既存の代数完備化の普遍性を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
def natAdicCompletionLift (q : R →+* S) (hc : IsAdicComplete (Ideal.span {(p : S)}) S) :
    AdicCompletion (Ideal.span {(p : R)}) R →+* S := by
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  exact (adicCompletionToCompleteAlgebra R (Ideal.span {(p : R)})
    (Submodule.fg_span (Set.toFinite _)) S).toRingHom
/-- ## 概要
p 進完備化からの標準延長は、元の R の各標準像上で与えられた環射と一致する。
BS Thm 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
元の環射が定める代数構造を局所導入し、既存の標準延長の係数像の公式を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
theorem natAdicCompletionLift_of (q : R →+* S) (hc : IsAdicComplete (Ideal.span {(p : S)}) S)
    (r : R) : natAdicCompletionLift p q hc
      (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) r) = q r := by
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  exact adicCompletionToCompleteAlgebra_of R (Ideal.span {(p : R)}) _ S r
/-- ## 概要
p 進完備な環への二つの環射が、完備化前の元の環の標準像上で一致すれば、両環射は一致する。
BS Thm 7.14（著者版 p.61）の極限段で用いる普遍性の補助命題。

## 方針
共通の元の環射により終域の代数構造を定め、両射をその上の代数射にして既存の一意性を使う。

## 規約
p は任意の自然数。p 正則性・Noether 性・元環の完備性は要求しない。

## 使われ方
p 完全忠実平坦な perfectoid 代数の圏の余極限の普遍性を検証する。
-/
theorem natAdicCompletion_ringHom_ext (hc : IsAdicComplete (Ideal.span {(p : S)}) S)
    (f g : AdicCompletion (Ideal.span {(p : R)}) R →+* S)
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g := by
  let q := f.comp (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R))
  let := q.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) S := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := S) (M := S)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hc
  let fa : AdicCompletion (Ideal.span {(p : R)}) R →ₐ[R] S :=
    { f with commutes' := fun r ↦ rfl }
  let ga : AdicCompletion (Ideal.span {(p : R)}) R →ₐ[R] S :=
    { g with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  exact congrArg AlgHom.toRingHom
    (adicCompletion_algHom_ext R (Ideal.span {(p : R)})
      (Submodule.fg_span (Set.toFinite _)) S fa ga)
end SerrePositivity.BhattScholze.Andre.Transfinite
