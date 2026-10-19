module

public import SerrePositivity.EInfinity.Operad.CoalgebraInterval
public import SerrePositivity.EInfinity.Operad.CoalgebraRestriction

/-!
# 余代数区間のオペラッド射に沿う制限

概要：Berger–Fresse §3.1 の区間を augmentation と両立するオペラッド射で制限する。
方針：余演算だけを制限し、底の区間・端点・収縮を保つ。
規約：オペラッド射の Hopf 対角保存は要求しない。
使われ方：table reduction に沿って区間切断作用を E-coalgebra 区間へ制限する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P Q : Operad A}

/-- 概要：単位上の余演算は augmentation の前合成と両立する（BF §3.1）。
方針：テンソルの合成保存則で係数射を分離する。
規約：任意のオペラッド射と augmentation に適用する。
使われ方：区間の端点・収縮の保存条件を制限へ移す。 -/
@[reassoc]
lemma unitCoaction_comp (f : P ⟶ Q) (ε : Q ⟶ commutativeOperad A) (n : ℕ) :
    unitCoaction (f ≫ ε) n = (f.map.app (FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫
      unitCoaction ε n := by
  change ((f.map.app _ ≫ ε.map.app _) ▷ (𝟙_ (Complex A))) ≫ _ = _
  simp only [comp_whiskerRight, unitCoaction, Category.assoc]

namespace CoalgebraInterval

/-- 概要：余代数区間をオペラッド射に沿って制限する（BF §3.1）。
方針：係数射と端点・収縮を交換し、元の可換図式を使う。
規約：底の cofibration と擬同型の証明は同じものを使う。
使われ方：χ の区間から TR に沿って E の区間を得る。 -/
def restrict (f : P ⟶ Q) {ε : Q ⟶ commutativeOperad A} (I : CoalgebraInterval ε) :
    CoalgebraInterval (f ≫ ε) where
  coalgebra := restrictCoalgebraObj f I.coalgebra
  endpoint := I.endpoint
  contraction := I.contraction
  endpoint_contraction := I.endpoint_contraction
  endpoint_coaction b n := by
    change (P.arity n ◁ I.endpoint b) ≫
      (f.map.app _ ▷ I.coalgebra.carrier) ≫ I.coalgebra.coaction n = _
    rw [whisker_exchange_assoc, unitCoaction_comp, Category.assoc]
    exact congrArg (fun h => (f.map.app (FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫ h)
      (I.endpoint_coaction b n)
  contraction_coaction n := by
    change ((f.map.app _ ▷ I.coalgebra.carrier) ≫ I.coalgebra.coaction n) ≫
      TensorPowers.map I.contraction n = _
    rw [Category.assoc, I.contraction_coaction, unitCoaction_comp]
    exact (whisker_exchange_assoc (f.map.app (FiniteBijection.of n)) I.contraction
      (unitCoaction ε n)).symm
  boundary_cofibration := I.boundary_cofibration
  contraction_quasiIso := I.contraction_quasiIso

end CoalgebraInterval

end SerrePositivity.EInfinity.Operad
