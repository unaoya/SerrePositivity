module
public import SerrePositivity.InfinityCategories.Derived.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Core.KanCharacterization
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp

/-! # Kan 基底上の屋根の右ファイブレーション

概要：Kan 基底上の右ファイブレーションの全空間は Kan で、射影は左にもなる。
方針：右ファイブレーションの可逆性の反映で全空間の h を亜群にし、全ホーンを持ち上げる。
規約：モデル構造の Fibration クラスは使わない。使われ方：商側の屋根の局所定値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet

/-- Kan 基底上の右ファイブレーションの全空間は Kan。 -/
lemma roofRightFibration_kanComplex {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [RightFibration p] : KanComplex E := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : IsGroupoid (hoFunctor.obj E) := by
    constructor
    intro x y f
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective x y f
    apply derived_rightFibration_reflects_invertibleEdge p e
    exact IsGroupoid.all_isIso (C := hoFunctor.obj B) _
  exact kanComplex_of_isGroupoid E

/-- Kan 複体間の右ファイブレーションは左ファイブレーションでもある。 -/
lemma roofRightFibration_leftFibration_of_kan {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [RightFibration p] : LeftFibration p where
  mem := by
    intro A Z j hj
    cases hj with
    | @intro n i hi =>
      exact rightFibration_hasLiftingProperty_horn_of_kanComplex p n i

end SerrePositivity.InfinityCategories
