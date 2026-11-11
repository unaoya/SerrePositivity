module
public import SerrePositivity.KST.SConstruction.PerfectVerdierDiagram
public import SerrePositivity.KST.Spectra.SpectrumFiberSquares
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-! # Cat^perf 上の Sp 値局所化不変量
概要：零・filtered 余極限・冪等完備 Verdier 列を保存する実 ∞ 関手を定義する。
方針：全 filtered ∞ 添字と実 join 余錐、元の coherent 四角形を直接条件に使う。
規約：連結 K がこの条件を満たすとは主張しない。使われ方：BGT (a) と Tamme・LT。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open Spectra
open scoped Simplicial

/-- Cat^perf の零安定対象を、同じ実 Sp 頂点の零対象へ送る条件。 -/
def PreservesPerfectZeroCategories (E : perfectStableInfinity.{u} ⟶ Sp.{u}) : Prop :=
  ∀ a : perfectStableInfinity.{u} _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject a) → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (E.app (Opposite.op ⦋0⦌) a)

/-- 全ての小さい filtered ∞ 添字の実余極限余錐を保存する条件。 -/
def PreservesPerfectFilteredColimits (E : perfectStableInfinity.{u} ⟶ Sp.{u}) : Prop :=
  ∀ (J : SSet.{u}) [Quasicategory J] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity J]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ perfectStableInfinity.{u})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone E c)

/-- BGT の局所化不変量の条件を、実 Cat^perf と Sp 値 ∞ 関手に課す。 -/
structure IsPerfectLocalizingInvariant (E : perfectStableInfinity.{u} ⟶ Sp.{u}) : Prop where
  preservesZero : PreservesPerfectZeroCategories E
  preservesFilteredColimits : PreservesPerfectFilteredColimits E
  preservesVerdier (d : PerfectVerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ E)

/-- 局所化不変量は、全高次単体上で定義された同じ Sp 値 ∞ 関手を保持する。 -/
structure PerfectLocalizingInvariant where
  hom : perfectStableInfinity.{u} ⟶ Sp.{u}
  isLocalizing : IsPerfectLocalizingInvariant hom

/-- 同じ Verdier 四角形の像を、元の零角を持つ Sp の三角形として保持する。 -/
def IsPerfectLocalizingInvariant.fiberTriangle
    {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)
    (d : PerfectVerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u} where
  square := d.square ≫ E
  zero_corner := hE.preservesZero _ d.zero_corner

/-- 同じ実 Verdier 図式の像は、元の Sp の fiber 列を与える。 -/
lemma IsPerfectLocalizingInvariant.fiberTriangle_isFiber
    {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)
    (d : PerfectVerdierDiagram.{u}) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence (hE.fiberTriangle d) :=
  hE.preservesVerdier d

end SerrePositivity.KST.SConstruction
