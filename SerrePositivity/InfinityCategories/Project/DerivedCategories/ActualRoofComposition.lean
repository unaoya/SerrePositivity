module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofOreRefinement
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionEdges

/-! # 共通細分上の実屋根の合成

概要：二つの実屋根に、共通細分と合成分母・分子を持つ実合成データを供給する。
方針：Ore 細分の共通対角を保ち、外側の二合成も実合成三角形で指定する。
規約：通常の屋根圏の厳密な合成関手や結合則はまだ主張しない。
使われ方：任意標的への商 Hom 作用と合成三角形の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 実分母と同じ始点の実分子を持つ、端点を指定した屋根。 -/
structure ActualRoofSpan {X : SSet.{u}} (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) where
  apex : X _⦋0⦌
  denominator : Truncated.Edge (X := (truncation 2).obj X) apex x
  denominator_mem : denominator.edge ∈ W
  numerator : Truncated.Edge (X := (truncation 2).obj X) apex y

/-- 二つの屋根の実合成は、共通細分の二三角形と外側の二合成三角形を保持する。 -/
structure ActualRoofComposition {X : SSet.{u}} (W : Set (X _⦋1⦌))
    {x y z : X _⦋0⦌} (r : ActualRoofSpan W x y) (s : ActualRoofSpan W y z)
    extends _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofOreRefinement W r.numerator s.denominator where
  combinedDenominator : Truncated.Edge (X := (truncation 2).obj X) apex x
  combinedDenominator_mem : combinedDenominator.edge ∈ W
  denominatorTriangle : Truncated.Edge.CompStruct denominator r.denominator combinedDenominator
  combinedNumerator : Truncated.Edge (X := (truncation 2).obj X) apex z
  numeratorTriangle : Truncated.Edge.CompStruct lift s.numerator combinedNumerator

/-- 実合成データが指定する、同じ共通始点の合成屋根。 -/
def ActualRoofComposition.composite {X : SSet.{u}} {W : Set (X _⦋1⦌)}
    {x y z : X _⦋0⦌} {r : ActualRoofSpan W x y} {s : ActualRoofSpan W y z}
    (C : ActualRoofComposition W r s) : ActualRoofSpan W x z :=
  ⟨C.apex, C.combinedDenominator, C.combinedDenominator_mem, C.combinedNumerator⟩

/-- 安定 ∞ 圏の二つの実 Verdier 屋根は、全四三角形を保つ実合成データを持つ。 -/
theorem cofiberStableEdges_actualRoofComposition_nonempty {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (P : Set (X _⦋0⦌)) {x y z : X _⦋0⦌}
    (r : ActualRoofSpan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {a | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P a}) x y)
    (s : ActualRoofSpan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {a | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P a}) y z) :
    Nonempty (ActualRoofComposition (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {a | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P a}) r s) := by
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberStableEdges_actualOreRefinement_nonempty P r.numerator s.denominator
    s.denominator_mem
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective R.apex x
    (Truncated.HomotopyCategory.homMk R.denominator ≫
      Truncated.HomotopyCategory.homMk r.denominator)
  obtain ⟨n, hn⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective R.apex z
    (Truncated.HomotopyCategory.homMk R.lift ≫ Truncated.HomotopyCategory.homMk s.numerator)
  obtain ⟨Td⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hd.symm
  obtain ⟨Tn⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hn.symm
  exact ⟨{ toActualRoofOreRefinement := R
           combinedDenominator := d
           combinedDenominator_mem :=
             (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_compStruct_twoOfThree P Td).1 R.denominator_mem r.denominator_mem
           denominatorTriangle := Td
           combinedNumerator := n
           numeratorTriangle := Tn }⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
