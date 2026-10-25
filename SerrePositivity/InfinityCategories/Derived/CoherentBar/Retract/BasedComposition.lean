module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedOperators
/-!
概要：始点を保つ単体写像の二段合成を、同じ実シフト単位ブロックへ照合する。
方針：端点の等式を明示し、既存のシフトブロックの合成則で中間シフトを消す。
規約：単体ラベル・全斉次次数・端点輸送を保持する。
使われ方：正規化境界の面と退化の有限和を、ラベル係数の合成へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

private lemma unitBlock_congr (a b : ℤ) (M N : RightModule R D) (h : M = N) :
    HEq (moduleHomShiftBlock R D a b (unitElement R M).val
      (by omega : a + 0 - b = a - b))
      (moduleHomShiftBlock R D a b (unitElement R N).val
        (by omega : a + 0 - b = a - b)) := by
  cases h
  rfl

lemma dgCoherentBarBasedBlock_comp_heq {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0)
    (g : ⦋l⦌ ⟶ ⦋m⦌) (hg : g.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    HEq (compose R
      (dgCoherentBarBasedBlock R D F g hg (I.map f.op s))
      (dgCoherentBarBasedBlock R D F f hf s)
      (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) =
        (n : ℤ) - (l : ℤ)))
      (dgCoherentBarBasedBlock R D F (g ≫ f) (by
        change f.toOrderHom (g.toOrderHom 0) = 0
        rw [hg, hf]) s) := by
  let M := dgCoherentBarSource R D F ⟨n, s⟩
  have hm := dgCoherentBarSource_based_map R D F f hf s
  have hl := (dgCoherentBarSource_based_map R D F g hg (I.map f.op s)).trans hm
  have hfg := gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl (congrArg (shiftModule (m : ℤ)) hm) (congrArg (shiftModule (l : ℤ)) hl)
    rfl rfl rfl
    (dgCoherentBarBasedBlock R D F g hg (I.map f.op s))
    (dgCoherentBarBasedBlock R D F f hf s)
    (moduleHomShiftBlock R D (m : ℤ) (l : ℤ) (unitElement R M).val (by omega))
    (moduleHomShiftBlock R D (n : ℤ) (m : ℤ) (unitElement R M).val (by omega))
    ((dgCoherentBarBasedBlock_heq R D F g hg (I.map f.op s)).trans
      (unitBlock_congr R D (m : ℤ) (l : ℤ) _ _ hm))
    (dgCoherentBarBasedBlock_heq R D F f hf s)
    (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ))
    (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ))
  have hcomp := moduleHomShiftBlock_comp R D (n : ℤ) (m : ℤ) (l : ℤ)
    (unitElement R M).val (unitElement R M).val
    (by omega : (n : ℤ) + 0 - (m : ℤ) = (n : ℤ) - (m : ℤ))
    (by omega : (m : ℤ) + 0 - (l : ℤ) = (m : ℤ) - (l : ℤ))
    (by omega : ((n : ℤ) - (m : ℤ)) + ((m : ℤ) - (l : ℤ)) = (n : ℤ) - (l : ℤ))
  rw [unit_compose] at hcomp
  exact hfg.trans ((heq_of_eq hcomp).trans
    (dgCoherentBarBasedBlock_heq R D F (g ≫ f) (by
      change f.toOrderHom (g.toOrderHom 0) = 0
      rw [hg, hf]) s).symm)

end SerrePositivity.InfinityCategories
