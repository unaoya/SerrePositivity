module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：等しい指定頂点で取った同じ射の fiber を、包含を保つ厳密な同型で結ぶ。
方針：指定頂点の等式に沿って fiber を移送する。
規約：元の全空間への包含を保持する。
使われ方：指定外ホーンの境界式と、元の比較の fiber を結ぶ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

variable {X Y : SSet.{u}} (p : X ⟶ Y) {b c : Y _⦋0⦌} (h : b = c)

/-- 同じ指定頂点の等式に沿う、元の fiber の厳密な同型。 -/
def vertexFiberPointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c :=
  eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)

/-- 同じ指定頂点の移送は、元の全空間への包含を保持する。 -/
lemma vertexFiberPointIso_hom_ι :
    (vertexFiberPointIso p h).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  subst c
  simp [vertexFiberPointIso]

/-- 逆向きの移送も、元の全空間への包含を保持する。 -/
lemma vertexFiberPointIso_inv_ι :
    (vertexFiberPointIso p h).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c := by
  subst c
  simp [vertexFiberPointIso]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
