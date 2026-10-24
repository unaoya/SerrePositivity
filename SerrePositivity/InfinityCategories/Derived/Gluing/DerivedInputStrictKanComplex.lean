module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputStrictEquivalence
/-! # 元入力を保つ同一対角引き戻しの Kan 性

概要：元左右 Hom 入力付きの厳密な同一対角引き戻しは Kan 複体である。
方針：終側入力対角の既存の Kan fibration と始側入力 fiber の Kan 性を用いる。
規約：入力を忘れず、主経路へモデル構造の instance 仮定を追加しない。
使われ方：入力付き path 模型の実逆射を厳密な同一対角模型へ移す。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingDerivedCompositionInputStrictPullback_kanComplex :
    KanComplex (dgGluingDerivedCompositionInputStrictPullback R C D M X Y) := by
  have hf := dgGluingDerivedFirstCompositionInputFiber_kanComplex R C D M X Y
  dsimp only [dgGluingDerivedFirstCompositionInputFiber] at hf
  have := dgGluingDerivedLastCompositionInputDiagonal_fibration R C D M X Y
  exact dgGluingKanPullback_of_leftFibration
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
end SerrePositivity.InfinityCategories
