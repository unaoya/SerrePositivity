module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofRelativeFiberHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofConePrism

/-! # 実錐による相対屋根問題の共通 fiber 還元

概要：底の実錐と全時刻で可換な二つの prism を一つの還元データに束ねる。
方針：底の錐の prism に相対持ち上げを適用し、零端を同じ fiber へ回収する。
規約：指定境界と全体は終端で厳密に保つ。使われ方：実屋根比較の任意有限相対問題。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A K E Q B : SSet.{u}} (i : A ⟶ K) (p : E ⟶ B) (q : Q ⟶ B)
variable (F : E ⟶ Q) (a : A ⟶ E) (g : K ⟶ Q)

/-- 共通底錐と、元の相対問題を同じ fiber へ戻す厳密な輸送。 -/
structure RoofRelativeFiberReduction where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (g ≫ q)
  prism : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFiberPrism i p q F a g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism cone)

variable {i p q F a g}
namespace RoofRelativeFiberReduction
variable (R : RoofRelativeFiberReduction i p q F a g)

/-- 元屋根境界の共通 fiber への還元。 -/
def boundary : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p R.cone.vertex :=
  R.prism.sourceFiber R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

/-- 商屋根全体の同じ共通 fiber への還元。 -/
def target : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q R.cone.vertex :=
  R.prism.targetFiber R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

/-- fiber 上の境界と全体の比較は厳密に可換。 -/
lemma square (hF : F ≫ q = p) :
    R.boundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q F hF R.cone.vertex = i ≫ R.target :=
  R.prism.fiber_square hF R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

/-- 還元後の元屋根境界から元の境界への実輸送。 -/
def boundaryTransport : SSet.Homotopy (R.boundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p R.cone.vertex) a :=
  R.prism.sourceHomotopy R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

/-- 還元後の商屋根全体から元の全体への実輸送。 -/
def targetTransport : SSet.Homotopy (R.target ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q R.cone.vertex) g :=
  R.prism.targetHomotopy R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

/-- 二つの輸送は境界全体・全時刻で比較と厳密に可換。 -/
lemma transport_boundary : (i ▷ (Δ[1] : SSet.{u})) ≫ R.targetTransport.h =
    R.boundaryTransport.h ≫ F :=
  R.prism.homotopy_boundary R.cone.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_zero R.cone)

end RoofRelativeFiberReduction

/-- 指定底錐から、相対問題の共通 fiber への全境界付き還元を構成する。 -/
theorem roofRelativeFiberReduction_of_cone [Mono i] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    (hF : F ≫ q = p) (ha : a ≫ F = i ≫ g) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (g ≫ q)) :
    Nonempty (RoofRelativeFiberReduction i p q F a g) := by
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeFiberPrism_nonempty i p q F a g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism c) hF ha
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofConePrism_one c).symm
  exact ⟨⟨c, T⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
