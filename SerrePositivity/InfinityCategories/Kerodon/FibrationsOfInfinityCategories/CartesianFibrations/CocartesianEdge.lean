module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：射に対する cocartesian な辺の外側ホーン充填条件。
方針：先頭の辺を固定した最初の外側ホーンの相対充填として定義する。
規約：モデル構造や straightening は使わない。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、Proposition 7.1.6.13（Tag 02XB） の錐の輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cocartesian な辺は、その辺を先頭に持つ外側ホーンを標的上で充填する辺。
方針：次元二以上の最初の外側ホーンを量化する。
規約：quasicategory 性や inner fibration 性は定義には含めない。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5） の cocartesian な辺。 -/
@[kerodon 01T5]
def HasCocartesianHornLifting {E B : SSet.{u}} (p : E ⟶ B) {x y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) : Prop :=
  ∀ (n : ℕ) (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ E) (β : (Δ[n + 2] : SSet.{u}) ⟶ B),
    σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = e.edge →
      σ ≫ p = (horn (n + 2) 0).ι ≫ β →
        ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ E, (horn (n + 2) 0).ι ≫ F = σ ∧ F ≫ p = β

/-- 概要：inner fibration に対する可逆な辺は cocartesian。
方針：既存の相対外側ホーン充填を使う。
規約：始域・標的は quasicategory。
使われ方：Kerodon Example 5.1.1.4（Tag 01T8） の可逆な輸送。 -/
lemma IsInvertibleEdge.hasCocartesianHornLifting {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] {x y : E _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    HasCocartesianHornLifting p e := by
  intro n σ β hσ hw
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hσ).2 he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_initialHorn p n σ β hw hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsInvertibleEdge (hasCocartesianHornLifting)


/-- 概要：可逆な基底の辺の上の cocartesian な辺は可逆。
方針：基底の外側ホーンを先に充填し、cocartesian 性で元へ持ち上げる。
規約：始域・標的は quasicategory、p 自身の inner fibration 性は不要。
使われ方：Kerodon §5.1.1（Tag 01T4） の退化した基底上の輸送の同型性。 -/
lemma HasCocartesianHornLifting.isInvertibleEdge_of_map {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {p : E ⟶ B} {x y : E _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y}
    (he : HasCocartesianHornLifting p e) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_of_hasInitialHornFillers e
  intro n σ hσ
  have hτ : (σ ≫ p).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
      (e.map ((truncation 2).map p)).edge := congrArg (p.app (Opposite.op ⦋1⦌)) hσ
  obtain ⟨β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge _ hp n (σ ≫ p) hτ
  obtain ⟨F, hF, _⟩ := he n σ β hσ hβ.symm
  exact ⟨F, hF⟩

/-- 概要：可逆な基底上では cocartesian 性と辺の可逆性は同値。
方針：二つの外側ホーン充填による方向を組み合わせる。
規約：p は quasicategory 間の inner fibration。
使われ方：Kerodon §5.1.1（Tag 01T4） の fiber 内の cocartesian な辺。 -/
@[kerodon 01T8]
lemma hasCocartesianHornLifting_iff_isInvertibleEdge_of_map {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {x y : E _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map p))) :
    HasCocartesianHornLifting p e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
  ⟨fun he ↦ he.isInvertibleEdge_of_map hp, fun he ↦ he.hasCocartesianHornLifting p⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
