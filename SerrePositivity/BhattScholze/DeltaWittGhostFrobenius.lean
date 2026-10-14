module

public import SerrePositivity.BhattScholze.DeltaWittGhostRingHom
public import Mathlib.RingTheory.WittVector.Frobenius

/-! # 構成したWitt写像のFrobenius図式とδ方程式

ghost成分の一段シフトを使い、δ構造を要求しない終域への係数射も扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- ghost射単射下では、構成したWitt元のFrobeniusは基底φの像。 -/
theorem deltaWittGhostVector_frobenius (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) :
    WittVector.frobenius (deltaWittGhostVector D a) =
      deltaWittGhostVector D (D.frobeniusLift a) := by
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply,
    WittVector.ghostComponent_frobenius, deltaWittGhostVector_ghostComponent,
    deltaWittGhostVector_ghostComponent]
  exact Function.iterate_succ_apply D.frobeniusLift n a

/-- 全Witt環射は基底FrobeniusとWitt Frobeniusを絡める。 -/
theorem deltaWittGhostRingHom_frobenius_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    WittVector.frobenius.comp (deltaWittGhostRingHom D hg) =
      (deltaWittGhostRingHom D hg).comp D.frobeniusLift := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_frobenius D hg a

/-- 基底δを使うFrobenius方程式。全Witt係数を追うための具体的な式。 -/
theorem deltaWittGhostVector_frobenius_formula (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) :
    WittVector.frobenius (deltaWittGhostVector D a) =
      (deltaWittGhostVector D a) ^ p +
        (p : WittVector p A) * deltaWittGhostVector D (D.delta a) := by
  rw [deltaWittGhostVector_frobenius D hg]
  change (deltaWittGhostRingHom D hg) (D.frobeniusLift a) = _
  rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
  rfl

/-- 任意通常係数射によるδ方程式の像。終域のδ構造は要求しない。 -/
theorem deltaWittGhostVector_frobenius_formula_map {B : Type v} [CommRing B]
    (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) :
    WittVector.map q (WittVector.frobenius (deltaWittGhostVector D a)) =
      (WittVector.map q (deltaWittGhostVector D a)) ^ p +
        (p : WittVector p B) * WittVector.map q (deltaWittGhostVector D (D.delta a)) := by
  rw [deltaWittGhostVector_frobenius_formula D hg, map_add, map_pow, map_mul, map_natCast]

end SerrePositivity.BhattScholze
