module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace
public import
  SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：任意の実単体族を、元の初期値を固定して left fibration へ持ち上げる。
方針：最初の頂点包含から零単体の同型因子を消去し、相対延長を使う。
規約：全係数を保持。使われ方：同じ実四面体から四面の比較を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の全係数を保った最初の頂点包含は left anodyne。 -/
lemma simplexPrismVertex_zero_leftAnodyne (n : ℕ) (P : SSet.{u}) :
    leftAnodyneExtensions (simplexPrismVertex n 0 P) := by
  have h := simplexPrismFirstVertex_leftAnodyne n P
  rw [scaffoldFirstVertex_whiskerRight] at h
  exact (leftAnodyneExtensions.cancel_left_of_respectsIso (snd (Δ[0] : SSet.{u}) P)
    (simplexPrismVertex n 0 P)).mp h

/-- 同じ実単体族の初期値を固定する持ち上げは、追加の整合性仮定なしに存在する。 -/
lemma exists_simplexInitialLift {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (n : ℕ) (β : (Δ[n] : SSet.{u}) ⊗ P ⟶ B) (v : P ⟶ E)
    (hv : v ≫ p = simplexPrismVertex n 0 P ≫ β) :
    ∃ W : (Δ[n] : SSet.{u}) ⊗ P ⟶ E,
      W ≫ p = β ∧ simplexPrismVertex n 0 P ≫ W = v :=
  exists_relativeFunctorExtension_of_leftAnodyne p β (simplexPrismVertex n 0 P)
    (simplexPrismVertex_zero_leftAnodyne n P) v hv

end SerrePositivity.InfinityCategories.F2
