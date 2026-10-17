module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionAlgebraUniversal

/-!
# André A1-a：p 完備化から完備環への環射

## 概要

通常の p 完備化から p 完備環への環射は、元の環からの射に一意に対応する。
BS Rem 7.15（著者版 p.62）の完備入力環の試験射に使う。

## 方針

指定環射で標的を代数にし、有限生成イデアルの完備代数への既存の普遍性を適用する。
原典の記述を補う、通常の加群完備化と係数射による経路。

## 規約

p の素数性・源の p 正則性は不要。標的には通常の p 完備性を要求する。

## 使われ方

未完備入力商からの射を、その p 完備化からの射へ延長する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable (R : Type u) [CommRing R] (p : ℕ)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "C" => AdicCompletion (Ideal.span {(p : R)}) R

/-- 概要：元の環射は p 完備化から p 完備環への一意な環射に延長する。
方針：環射で指定した代数作用のもとで、完備代数への一意な代数射を環射に戻す。
規約：p 正則性や Noether 性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力環からの射。 -/
theorem existsUnique_primeAdicCompletionHom (k : R →+* B) :
    ∃! F : C →+* B, F.comp (algebraMap R C) = k := by
  let := k.toAlgebra
  let : IsAdicComplete (Ideal.span {(p : R)}) B := by
    apply (IsAdicComplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := B) (M := B)).mp
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
      (inferInstance : IsAdicComplete (Ideal.span {(p : B)}) B)
  obtain ⟨F, _, hu⟩ := adicCompletion_existsUnique_algHom R
    (Ideal.span {(p : R)}) (Submodule.fg_span_singleton _) B
  refine ⟨F.toRingHom, ?_, ?_⟩
  · exact RingHom.ext F.commutes
  · intro G hG
    let G' : C →ₐ[R] B := { G with commutes' := RingHom.congr_fun hG }
    exact congrArg AlgHom.toRingHom (hu G' trivial)

/-- 概要：p 完備化から p 完備環への環射は元の環上の値で決まる。
方針：同じ元の環射を延長する二つの射の一意性を使う。
規約：環射に連続性を追加指定する必要はない。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力射の一意性。 -/
theorem primeAdicCompletion_ringHom_ext (F G : C →+* B)
    (h : F.comp (algebraMap R C) = G.comp (algebraMap R C)) : F = G := by
  obtain ⟨K, _, hu⟩ := existsUnique_primeAdicCompletionHom R p (G.comp (algebraMap R C))
  exact (hu F h).trans (hu G rfl).symm

end SerrePositivity.BhattScholze.Andre
