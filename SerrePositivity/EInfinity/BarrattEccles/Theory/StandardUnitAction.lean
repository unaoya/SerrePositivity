module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.StandardHopfInput
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerBlockSwap

/-!
# 標準語の単位入力と自由代数の作用

HA 3.2.4.7 の指定係数射を、代数の同じ作用へ移す（BS-W16 L14・L15）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebra
variable (R : Type u) [CommRing R]

/-- 前半の色への係数射は、後半を指定単位で評価する同じ作用を与える。 -/
lemma twoColorLeftCoefficient_action (Z : (operad R).Algebra) (m n : ℕ) :
    (twoColorLeftCoefficient R m n ▷ power Z.carrier m) ≫ Z.action m =
    ((operad R).arity (m + n) ◁ ((ρ_ (power Z.carrier m)).inv ≫
      (power Z.carrier m ◁ nullaryUnitPower R Z n) ≫
      (appendIso Z.carrier m n).hom)) ≫ Z.action (m + n) := by
  rw [twoColorLeftCoefficient, comp_whiskerRight_assoc, nullaryPrefixDelete_action]
  rw [← algebra_action_bijection Z (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n)]
  simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
  simp only [← whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc]
  congr 2
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_blockSwap]
  rw [← id_tensorHom, BraidedCategory.braiding_naturality_assoc]
  rw [braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_id]

variable (X Y : Complex R)

/-- 左の自由生成元を残す単位代入の作用は、指定左係数射の後の Schur 生成射。 -/
lemma freeLeftUnitExtension_action (m n : ℕ) :
    ((operad R).arity (m + n) ◁ freeLeftUnitExtension R X m n) ≫
      ((operad R).freeAlgebra X).action (m + n) =
    (twoColorLeftCoefficient R m n ▷ power X m) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι R (sequence R) X m := by
  dsimp only [freeLeftUnitExtension]
  rw [tensorHom_def, Category.assoc, ← rightUnitor_inv_naturality_assoc]
  rw [whiskerLeft_comp, Category.assoc]
  erw [← twoColorLeftCoefficient_action R ((operad R).freeAlgebra X) m n]
  erw [whisker_exchange_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurAction_generators]
  rfl

/-- 右の自由生成元を残す単位代入の作用は、指定右係数射の後の Schur 生成射。 -/
lemma freeRightUnitExtension_action (m n : ℕ) :
    ((operad R).arity (m + n) ◁ freeRightUnitExtension R Y m n) ≫
      ((operad R).freeAlgebra Y).action (m + n) =
    (twoColorRightCoefficient R m n ▷ power Y n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι R (sequence R) Y n := by
  dsimp only [freeRightUnitExtension, twoColorRightCoefficient]
  rw [tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc]
  rw [whiskerLeft_comp, Category.assoc]
  erw [← nullaryPrefixDelete_action R ((operad R).freeAlgebra Y) m n]
  erw [whisker_exchange_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurAction_generators]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
