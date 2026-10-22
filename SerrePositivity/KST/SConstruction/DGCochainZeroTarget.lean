module
public import SerrePositivity.DifferentialGraded.Complexes.Zero

/-! # 実零複体を標的とする全 cochain の零性
概要：標的の実零対象性から、全整数次数の比較 cochain の零性を得る。
方針：零の恒等鎖写像を各次数へ評価し、各成分射の零性を判定する。
規約：cohomology の消滅だけでは代用しない。使われ方：右軸 Hom の厳密な一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R]

/-- 実零複体を標的とする全次数 cochain は、同じ零 cochain そのもの。 -/
lemma dgCochain_eq_zero_of_isZero_target {K T : Complex R} (hT : IsZero T)
    (n : ℤ) (c : Cochain K T n) : c = 0 := by
  apply Cochain.ext
  intro p q hpq
  have hi := congrArg (fun f : T ⟶ T => f.f q) ((IsZero.iff_id_eq_zero T).mp hT)
  have hq : IsZero (T.X q) := (IsZero.iff_id_eq_zero _).mpr hi
  exact hq.eq_of_tgt _ _

end SerrePositivity.KST.SConstruction
