module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathPullbackCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackHomotopySquare
/-! # 全正方形から一段 path 引き戻し内の実ホモトピーへ

概要：指定した path の全正方形と二入力の変形を、一段の引き戻しの同じ三座標へ移す。
方針：F2 の実引き戻し内ホモトピーを、既存の厳密な座標同型で輸送する。
規約：path・二入力・全円柱を選び直さない。
使われ方：④の指定境界から⑤の正本入力付き path 比較の実ホモトピーを構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K A B Z : SSet.{u}} (f : A ⟶ Z) (g : B ⟶ Z)
  (a : K ⟶ A) (b : K ⟶ B) (H : SSet.Homotopy (a ≫ f) (b ≫ g))

def dgGluingIntervalPathPullbackPoint : K ⟶ pullback (F2.arrowEndpointPair Z) (f ⊗ₘ g) :=
  F2.intervalPullbackHomotopyPoint f g a b H ≫ (dgGluingIntervalPathCoordinatesIso f g).hom

lemma dgGluingIntervalPathPullbackPoint_path :
    dgGluingIntervalPathPullbackPoint f g a b H ≫ pullback.fst _ _ =
      dgGluingHomotopyIntervalPath H := by
  rw [dgGluingIntervalPathPullbackPoint, Category.assoc,
    dgGluingIntervalPathCoordinatesIso_path, F2.intervalPullbackHomotopyPoint_path]
  rfl

lemma dgGluingIntervalPathPullbackPoint_inputs :
    dgGluingIntervalPathPullbackPoint f g a b H ≫ pullback.snd _ _ = lift a b := by
  rw [dgGluingIntervalPathPullbackPoint, Category.assoc,
    dgGluingIntervalPathCoordinatesIso_inputs]
  simp only [F2.intervalPullbackInputPair, comp_lift,
    F2.intervalPullbackHomotopyPoint_left, F2.intervalPullbackHomotopyPoint_right]

lemma dgGluingIntervalPathPullbackPoint_eq_of_coordinates
    (W : K ⟶ pullback (F2.arrowEndpointPair Z) (f ⊗ₘ g))
    (hp : dgGluingHomotopyIntervalPath H = W ≫ pullback.fst _ _)
    (hi : lift a b = W ≫ pullback.snd _ _) :
    dgGluingIntervalPathPullbackPoint f g a b H = W := by
  apply pullback.hom_ext
  · exact (dgGluingIntervalPathPullbackPoint_path f g a b H).trans hp
  · exact (dgGluingIntervalPathPullbackPoint_inputs f g a b H).trans hi

variable {a₀ a₁ : K ⟶ A} {b₀ b₁ : K ⟶ B}
  (H₀ : SSet.Homotopy (a₀ ≫ f) (b₀ ≫ g)) (H₁ : SSet.Homotopy (a₁ ≫ f) (b₁ ≫ g))
  (U : SSet.Homotopy a₀ a₁) (V : SSet.Homotopy b₀ b₁)
  (G : SSet.Homotopy H₀.h H₁.h)
  (h₀ : ((ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = U.h ≫ f)
  (h₁ : ((ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = V.h ≫ g)

def dgGluingIntervalPathPullbackHomotopyOfSquare :
    SSet.Homotopy (dgGluingIntervalPathPullbackPoint f g a₀ b₀ H₀)
      (dgGluingIntervalPathPullbackPoint f g a₁ b₁ H₁) :=
  functorHomotopyPostcomp (F2.intervalPullbackHomotopyOfSquare f g H₀ H₁ U V G h₀ h₁)
    (dgGluingIntervalPathCoordinatesIso f g).hom
end SerrePositivity.InfinityCategories
