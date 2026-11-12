module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedCylinderPrismSpace
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
概要：任意のパラメーターを持つ写像円柱上の射の厳密な貼り合わせ。
方針：パラメーターとの直積が pushout を保存することを使う。
規約：prism と終点の族の両方を全高次パラメーターで保つ。
使われ方：prism の中間空間から実際の円柱上の関手空間への比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：写像円柱の pushout は任意のパラメーターとの直積でも pushout。
方針：tensorRight の余極限保存を使う。
規約：元の関手 f とパラメーターは任意。
使われ方：prism と終点の族を貼り合わせる普遍性。 -/
theorem parametrizedCylinderIsPushout {K J : SSet.{u}} (f : K ⟶ J) (L : SSet.{u}) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ L) (f ▷ L)
      (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) :=
  (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f).map (tensorRight L)

/-- 概要：prism と終点の族を円柱とパラメーターの直積上に貼る。
方針：パラメーター付き pushout の desc を取る。
規約：両族の共通端での一致を厳密に要求する。
使われ方：全 lift prism の空間から実際の円柱上の射の族への写像。 -/
def parametrizedCylinderDesc {K J L E : SSet.{u}} (f : K ⟶ J)
    (H : (Δ[1] ⊗ K) ⊗ L ⟶ E) (G : J ⊗ L ⟶ E)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ L) ≫ H = (f ▷ L) ≫ G) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ⊗ L ⟶ E :=
  (parametrizedCylinderIsPushout f L).desc H G w

/-- 概要：貼り合わせた族の円柱部分は元の prism。
方針：pushout の第一包含と desc の計算則。
規約：全高次パラメーターでの等式。
使われ方：円柱上の関手の prism の回収。 -/
lemma parametrizedCylinderDesc_inl {K J L E : SSet.{u}} (f : K ⟶ J)
    (H : (Δ[1] ⊗ K) ⊗ L ⟶ E) (G : J ⊗ L ⟶ E)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ L) ≫ H = (f ▷ L) ≫ G) :
    (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ parametrizedCylinderDesc f H G w = H :=
  (parametrizedCylinderIsPushout f L).inl_desc H G w

/-- 概要：貼り合わせた族の終点部分は元の終点の族。
方針：pushout の第二包含と desc の計算則。
規約：全高次パラメーターでの等式。
使われ方：指定した終点の比較を厳密に保つ。 -/
lemma parametrizedCylinderDesc_inr {K J L E : SSet.{u}} (f : K ⟶ J)
    (H : (Δ[1] ⊗ K) ⊗ L ⟶ E) (G : J ⊗ L ⟶ E)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ L) ≫ H = (f ▷ L) ≫ G) :
    (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ parametrizedCylinderDesc f H G w = G :=
  (parametrizedCylinderIsPushout f L).inr_desc H G w

/-- 概要：円柱上の二つの族は prism と終点で一致すれば等しい。
方針：パラメーター付き pushout の一意性。
規約：始点だけの一致ではなく prism 全体の一致を要求する。
使われ方：円柱上の族と中間空間の往復の厳密な回収。 -/
lemma parametrizedCylinder_hom_ext {K J L E : SSet.{u}} (f : K ⟶ J)
    {F G : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ⊗ L ⟶ E}
    (hH : (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ F =
      (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ G)
    (hJ : (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ F =
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) f ▷ L) ≫ G) : F = G :=
  (parametrizedCylinderIsPushout f L).hom_ext hH hJ

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
