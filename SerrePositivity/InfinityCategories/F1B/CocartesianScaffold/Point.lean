module

public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.Definition
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementPoint

/-!
概要：一点の薄い圏を底とする cocartesian scaffold の全空間の比較。
方針：底の全単体の一意性で元の全空間と fiber を同定し、係数値の比較の同値性を使う。
規約：始域の simplicial replacement の quasicategory 性も係数値との同型から構成する。
使われ方：Kerodon Theorem 5.3.5.7、通常の有限順序の長さ零での帰納法の初期条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 概要：一点の薄い圏上の quasicategory 値図式の simplicial replacement は quasicategory。
方針：係数値との標準同型でホーンを移し、充填を全空間へ戻す。
規約：指定した対象 c の係数値にのみ quasicategory 性を要求する。
使われ方：Kerodon Theorem 5.3.5.7、長さ零の帰納段階での全空間の構造。 -/
lemma simplicialReplacementPoint_quasicategory
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) [Quasicategory (F.obj c)] :
    Quasicategory (simplicialReplacement F) := by
  let e := asIso (simplicialReplacementConstantLift F c)
  constructor
  intro n i a h₀ hn
  obtain ⟨H, hH⟩ := Quasicategory.hornFilling h₀ hn (a ≫ e.inv)
  refine ⟨H ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：一点の薄い圏上の cocartesian scaffold は全空間の前合成の同値条件を満たす。
方針：係数値からの同型と fiber からの同型の間の比較を、fiber 比較の同値へ帰着する。
規約：結論は任意の quasicategory を標的とする前合成の同値性。
使われ方：Kerodon Theorem 5.3.5.7、有限順序上の scaffold 比較の初期条件。 -/
lemma CocartesianScaffold.isPrecompositionEquivalence_of_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} {p : E ⟶ nerve C} [CocartesianFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : SerrePositivity.InfinityCategories.CocartesianScaffold p F l) (c : C) :
    IsPrecompositionEquivalence l := by
  have := simplicialReplacementPoint_quasicategory F c
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : IsIso (vertexFiberι p (nerveVertex c)) := SerrePositivity.InfinityCategories.vertexFiberι_isIso_of_nervePoint p c
  let h := hs.projection
  have hf := hs.fiber
  have hc : simplicialReplacementConstantLift F c ≫ l =
      SerrePositivity.InfinityCategories.leftScaffoldFiberMap p F l h c ≫ vertexFiberι p (nerveVertex c) := rfl
  have he : IsQCatEquivalence (simplicialReplacementConstantLift F c ≫ l) := by
    rw [hc]
    exact (hf c).comp
      (qCatEquivalenceOfIso (asIso (vertexFiberι p (nerveVertex c)))).isQCatEquivalence
  exact ((qCatEquivalenceOfIso (asIso (simplicialReplacementConstantLift F c))).isQCatEquivalence
    |>.cancel_left he).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
