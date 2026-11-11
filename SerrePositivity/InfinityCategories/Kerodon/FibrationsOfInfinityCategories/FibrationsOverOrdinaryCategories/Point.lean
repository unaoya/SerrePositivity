module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementPoint

/-!
概要：一点の薄い圏を底とする cocartesian scaffold の全空間の比較。
方針：底の全単体の一意性で元の全空間と fiber を同定し、係数値の比較の同値性を使う。
規約：始域の simplicial replacement の quasicategory 性も係数値との同型から構成する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、通常の有限順序の長さ零での帰納法の初期条件。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：一点の薄い圏上の quasicategory 値図式の simplicial replacement は quasicategory。
方針：係数値との標準同型でホーンを移し、充填を全空間へ戻す。
規約：指定した対象 c の係数値にのみ quasicategory 性を要求する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、長さ零の帰納段階での全空間の構造。 -/
lemma simplicialReplacementPoint_quasicategory
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) [Quasicategory (F.obj c)] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) := by
  let e := asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c)
  constructor
  intro n i a h₀ hn
  obtain ⟨H, hH⟩ := Quasicategory.hornFilling h₀ hn (a ≫ e.inv)
  refine ⟨H ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：一点の薄い圏上の cocartesian scaffold は全空間の前合成の同値条件を満たす。
方針：係数値からの同型と fiber からの同型の間の比較を、fiber 比較の同値へ帰着する。
規約：結論は任意の quasicategory を標的とする前合成の同値性。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限順序上の scaffold 比較の初期条件。 -/
lemma CocartesianScaffold.isPrecompositionEquivalence_of_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} {p : E ⟶ nerve C} [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E} (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence l := by
  have := simplicialReplacementPoint_quasicategory F c
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiberι_isIso_of_nervePoint p c
  let h := hs.projection
  have hf := hs.fiber
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c ≫ l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftScaffoldFiberMap p F l h c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := rfl
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c ≫ l) := by
    rw [hc]
    exact (hf c).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))).isQCatEquivalence
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c))).isQCatEquivalence
    |>.cancel_left he).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
