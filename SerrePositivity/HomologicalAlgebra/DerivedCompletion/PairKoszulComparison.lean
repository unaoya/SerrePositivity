module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairKoszulTransition
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerUnit
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIso

/-! # 二座標Koszul塔の元の表示と具体的な錐表示の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category
variable (R : Type u) [CommRing R]

/-- 有限段の表示同型は、元のKoszul遷移と可換する。 -/
theorem pairKoszulStageIso_naturality (f d : R) (n : ℕ) :
    (pairKoszulStageIso R f d (n + 1)).hom ≫ pairKoszulTransition R f d n =
      powerKoszulTransition R (pairKoszulCoordinates R f d) n ≫
        (pairKoszulStageIso R f d n).hom := by
  simp only [pairKoszulStageIso, pairKoszulTower, powerKoszulTower,
    koszulComplex_succ, eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  simp only [powerKoszulTransition, pairKoszulTransition, pairKoszulTransitionArrow,
    koszulComplexMapOfMul, pairKoszulCoordinates,
    Fin.snoc_last, Fin.init_snoc]
  rfl

/-- 二座標塔の具体的な錐表示による、実際のホモトピー逆極限。 -/
def pairKoszulCompletionComplex (f d : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (pairKoszulTower R f d) (pairKoszulTransition R f d)

/-- 元のKoszul完備化複体と具体的な塔表示の完備化複体との同型。
有限段のH⁰だけの比較ではなく、直積・mapping cone・シフト全体を比較する。 -/
def pairKoszulCompletionIso (f d : R) :
    koszulCompletionComplex R (pairKoszulCoordinates R f d) ≅ pairKoszulCompletionComplex R f d :=
  complexTowerHomotopyLimitIso R (powerKoszulTransition R (pairKoszulCoordinates R f d))
    (pairKoszulTransition R f d) (pairKoszulStageIso R f d)
      (fun n ↦ (pairKoszulStageIso_naturality R f d n).symm)

end SerrePositivity.DerivedCompletion
