module
public import SerrePositivity.KST.Fibration.VerdierKZeroSurjectivity
public import SerrePositivity.KST.SConstruction.DGKFixedInterface

/-! # 固定 ν の同じ厳密 dg 辺に沿う三角圏 K₀ と零次 cofinality

固定界面の安定値・辺だけを入力する。固定 K の Sp 値の π₀ との比較は主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 同じ固定 dg 入力辺の ν 像が誘導する、元の三角圏 K₀ の実準同型。 -/
def dgNuKZeroMap {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A P).obj) →+
      TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A Q).obj) :=
  stableKZeroMap (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A P) (dgKInputStableValue A Q) from
    dgKInputNuMap A f)

/-- この準同型は、固定 ν の辺と同定された元の dg 延長完全関手の作用そのもの。 -/
theorem dgNuKZeroMap_eq {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    dgNuKZeroMap A f = stableKZeroMap (presentedPerfectDGExactMap A f) := by
  unfold dgNuKZeroMap
  exact congrArg stableKZeroMap (dgKInputNuMap_eq A f)

/-- 同じ厳密 dg 列の ν 像が Verdier 列なら、元の商辺の三角圏 K₀ 作用は全射。 -/
theorem dgNuKZeroMap_surjective_of_verdier
    {P Q R : PerfDGInput.{u, v} A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A P) (dgKInputStableValue A Q) from dgKInputNuMap A f)
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A Q) (dgKInputStableValue A R) from dgKInputNuMap A g)) :
    Function.Surjective (dgNuKZeroMap A g) :=
  verdierKZeroMap_surjective h

end SerrePositivity.KST.Fibration
