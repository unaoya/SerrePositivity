module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraRestriction

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：単位上の余演算は augmentation の前合成と両立する（BF §3.1）。
方針：テンソルの合成保存則で係数射を分離する。
規約：任意のオペラッド射と augmentation に適用する。
使われ方：区間の端点・収縮の保存条件を制限へ移す。 -/
@[reassoc]
lemma unitCoaction_comp (f : P ⟶ Q) (ε : Q ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction (f ≫ ε) n = (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction ε n := by
  change ((f.map.app _ ≫ ε.map.app _) ▷ (𝟙_ (Complex A))) ≫ _ = _
  simp only [comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction, Category.assoc]

namespace CoalgebraInterval

/-- 概要：余代数区間をオペラッド射に沿って制限する（BF §3.1）。
方針：係数射と端点・収縮を交換し、元の可換図式を使う。
規約：底の cofibration と擬同型の証明は同じものを使う。
使われ方：χ の区間から TR に沿って E の区間を得る。 -/
def restrict (f : P ⟶ Q) {ε : Q ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A} (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval (f ≫ ε) where
  coalgebra := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictCoalgebraObj f I.coalgebra
  endpoint := I.endpoint
  contraction := I.contraction
  endpoint_contraction := I.endpoint_contraction
  endpoint_coaction b n := by
    change (P.arity n ◁ I.endpoint b) ≫
      (f.map.app _ ▷ I.coalgebra.carrier) ≫ I.coalgebra.coaction n = _
    rw [whisker_exchange_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction_comp, Category.assoc]
    exact congrArg (fun h => (f.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ (𝟙_ (Complex A))) ≫ h)
      (I.endpoint_coaction b n)
  contraction_coaction n := by
    change ((f.map.app _ ▷ I.coalgebra.carrier) ≫ I.coalgebra.coaction n) ≫
      _root_.SerrePositivity.TensorPowers.map I.contraction n = _
    rw [Category.assoc, I.contraction_coaction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction_comp]
    exact (whisker_exchange_assoc (f.map.app (_root_.SerrePositivity.FiniteBijection.of n)) I.contraction
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction ε n)).symm
  boundary_cofibration := I.boundary_cofibration
  contraction_quasiIso := I.contraction_quasiIso

end CoalgebraInterval

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
