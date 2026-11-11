module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiChartEquivalence
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiTransport
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UliftPiZeroComparison
/-!
概要：追加宇宙の全基点チャートを元の Kan 空間へ戻す。
方針：全基点 π の宇宙同型と指定道円柱の持ち上げを使う。
規約：元の射とその像の基点を同時に保持する。
使われ方：線形 coslice 比較の追加宇宙を除いて native 評価の五条件へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
  {n : ℕ} {A : Type w} {B : Type w'}

def DGBarCompactPiChart.ofUlift
    (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart ((SSet.uliftFunctor.{v, u}).obj X) n A) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart X n A where
  equiv x := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n x).toEquiv.trans (c.equiv (ULift.up x))
  of_transport e a b h := c.of_transport
    (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{v, u}).obj X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e.toTruncated)) _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport_ulift n e h)

lemma dgBarCompactPiChart_naturality_of_ulift
    (c : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart ((SSet.uliftFunctor.{v, u}).obj X) n A)
    (c' : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactPiChart ((SSet.uliftFunctor.{v, u}).obj Y) n B)
    (f : X ⟶ Y) (φ : A → B)
    (h : ∀ z a, c'.equiv (((SSet.uliftFunctor.{v, u}).map f).app _ z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n ((SSet.uliftFunctor.{v, u}).map f) z a) = φ (c.equiv z a))
    (x : X _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    c'.ofUlift.equiv (f.app _ x) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n f x a) = φ (c.ofUlift.equiv x a) := by
  exact (congrArg (c'.equiv (ULift.up (f.app _ x)))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv_naturality.{u, v} f n x a)).trans
      (h (ULift.up x) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiEquiv.{u, v} X n x a))

def dgBarCompactPiZeroChart_ofUlift
    (c : SSet.π₀ ((SSet.uliftFunctor.{v, u}).obj X) ≃ A) : SSet.π₀ X ≃ A :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiZeroEquiv.{u, v} X).trans c

lemma dgBarCompactPiZeroChart_naturality_of_ulift
    (c : SSet.π₀ ((SSet.uliftFunctor.{v, u}).obj X) ≃ A)
    (c' : SSet.π₀ ((SSet.uliftFunctor.{v, u}).obj Y) ≃ B) (f : X ⟶ Y) (φ : A → B)
    (h : ∀ a, c' (SSet.mapπ₀ ((SSet.uliftFunctor.{v, u}).map f) a) = φ (c a))
    (a : SSet.π₀ X) :
    dgBarCompactPiZeroChart_ofUlift c' (SSet.mapπ₀ f a) =
      φ (dgBarCompactPiZeroChart_ofUlift c a) :=
  (congrArg c' (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiZeroEquiv_naturality.{u, v} f a)).trans
    (h (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUliftPiZeroEquiv.{u, v} X a))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
