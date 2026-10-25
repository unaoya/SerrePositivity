module

public import SerrePositivity.BhattScholze.Delta.DeltaRing

/-! # 長さ2のWitt環の係数写像

環準同型をW₂の各座標に適用する。δ切断の自然性や商構成で共通に使う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- 環準同型をW₂の各座標に適用する射。δ切断の自然性を表すために使う。 -/
def wittTwoMap (f : A →+* B) : WittTwo p A →+* WittTwo p B :=
  RingHom.liftOfRightInverse (WittVector.truncate 2) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate 2).comp (WittVector.map f), by
      intro x hx
      change (WittVector.truncate 2) (WittVector.map f x) = 0
      apply (WittVector.mem_ker_truncate (p := p) 2 (WittVector.map f x)).mpr
      intro i hi
      rw [WittVector.map_coeff, (WittVector.mem_ker_truncate 2 x).mp hx i hi, map_zero]⟩

/-- W₂上の射は各Witt座標に元の環準同型を適用する。 -/
@[simp] theorem wittTwoMap_coeff (f : A →+* B) (x : WittTwo p A) (i : Fin 2) :
    (wittTwoMap (p := p) f x).coeff i = f (x.coeff i) := by
  change ((WittVector.truncate 2) (WittVector.map f x.out)).coeff i = _
  rw [WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_out]

end SerrePositivity.BhattScholze
