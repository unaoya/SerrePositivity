module

public import SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationSquare
public import Mathlib.Algebra.Exact.Basic

/-!
概要：有限変更の Frobenius 四角形を加法群の短完全列にまとめる。
方針：左辺は二つの制限の組、右辺は二つの制限の差とする。
規約：中心外の仮定は局所化した実際の代数写像の全射性。
使われ方：BST13 の有限変更の議論から射影 Čech の次数零へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
variable (f : A →+* B) (I : Ideal A)
local notation "PA" => FrobeniusDirectLimit A p hp hA
local notation "PB" => FrobeniusDirectLimit B p hp hB
local notation "PC" => FrobeniusDirectLimit (A ⧸ I) p hp (frobeniusQuotientPrimeCast p hA I)
local notation "PD" => FrobeniusDirectLimit (B ⧸ I.map f) p hp
  (frobeniusQuotientPrimeCast p hB (I.map f))

/-- 有限変更の四角形の左の加法写像：二つの実際の制限の組。 -/
def frobeniusCenterPair : PA →+ PB × PC where
  toFun a := (frobeniusDirectLimitMap p hp hA hB f a,
    frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA I) (Ideal.Quotient.mk I) a)
  map_zero' := by simp
  map_add' a b := by simp

/-- 有限変更の四角形の右の加法写像：二つの実際の制限の差。 -/
def frobeniusCenterDifference : PB × PC →+ PD where
  toFun bc := frobeniusDirectLimitMap p hp hB
      (frobeniusQuotientPrimeCast p hB (I.map f)) (Ideal.Quotient.mk (I.map f)) bc.1 -
    frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA I)
      (frobeniusQuotientPrimeCast p hB (I.map f))
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) bc.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel

/-- 中心の四角形の二つの加法写像の合成は零。 -/
theorem frobeniusCenterDifference_pair (a : PA) :
    frobeniusCenterDifference p hp hA hB f I (frobeniusCenterPair p hp hA hB f I a) = 0 := by
  obtain ⟨n, a, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) a
  exact sub_self _

/-- Spec 全射で中心外が局所全射な有限環拡大の、指定中心の加法群の短完全性。 -/
theorem frobeniusFiniteModification_exact [Algebra A B] [Module.Finite A B]
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (hI : I.FG)
    (hloc : ∀ P : PrimeSpectrum A, P ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl (Algebra.linearMap A B))) :
    Function.Injective (frobeniusCenterPair p hp hA hB (algebraMap A B) I) ∧
    Function.Exact (frobeniusCenterPair p hp hA hB (algebraMap A B) I)
      (frobeniusCenterDifference p hp hA hB (algebraMap A B) I) ∧
    Function.Surjective (frobeniusCenterDifference p hp hA hB (algebraMap A B) I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply frobeniusDirectLimitMap_injective_of_surjectiveSpectrum p hp hA hB (algebraMap A B) hs
    exact congrArg Prod.fst hab
  · intro bc
    constructor
    · intro hz
      have he := sub_eq_zero.mp hz
      obtain ⟨a, ha, hc⟩ := frobeniusFiniteModificationSquare_lift p hp hA hB hs I hI hloc
        bc.1 bc.2 he
      exact ⟨a, Prod.ext ha hc⟩
    · rintro ⟨a, rfl⟩
      exact frobeniusCenterDifference_pair p hp hA hB (algebraMap A B) I a
  · intro d
    obtain ⟨b, hb⟩ := frobeniusConductorSquare_quotient_surjective p hp hB
      (I.map (algebraMap A B)) d
    refine ⟨(b, 0), ?_⟩
    change _ - _ = d
    rw [map_zero, sub_zero]
    exact hb

end SerrePositivity.AlgebraicGeometry
