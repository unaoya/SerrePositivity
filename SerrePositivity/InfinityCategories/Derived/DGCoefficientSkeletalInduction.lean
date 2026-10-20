module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalInitial
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalSuccessor

/-! # 係数骨格状態の有限帰納

概要：指定部分と商全体の厳密正方形から、任意の有限骨格次数の係数状態を構成する。
方針：恒等閉分母の零段から、一段更新を自然数の帰納法で反復する。
規約：全段で元の部分図式を比較の全時刻で固定する。使われ方：有限対の全体充填。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] [K.Finite]
variable (x y : D) (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 任意の有限相対骨格次数に、同じ部分図式を保持する係数状態が存在する。 -/
theorem dgCoefficientSkeletalStage_nonempty (hP : localKFlat A D P)
    (ha : a ≫ pinchedHomChainMap ((inclusion A D P).map x y) = i ≫ g) (n : ℕ) :
    Nonempty (DGCoefficientSkeletalStage A D P i n x y a g) := by
  induction n with
  | zero => exact dgCoefficientSkeletalInitial_nonempty A D P i x y a g ha
  | succ n ih =>
    obtain ⟨S⟩ := ih
    exact dgCoefficientSkeletalSuccessor_nonempty A D P i n x y a g hP S

end SerrePositivity.InfinityCategories
