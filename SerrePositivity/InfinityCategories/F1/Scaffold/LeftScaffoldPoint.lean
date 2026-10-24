module

public import SerrePositivity.InfinityCategories.F1.Scaffold.LeftScaffold
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementPoint

/-!
概要：一点の薄い圏を底とする left scaffold の全空間の比較。
方針：底の全単体の一意性で元の全空間と fiber を同定し、係数値の比較の同値性を使う。
規約：始域の simplicial replacement の Kan 性も係数値との同型から構成する。
使われ方：Kerodon Theorem 5.3.5.7、通常の有限順序の長さ零での帰納法の初期条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：一点の薄い圏上の Kan 値図式の simplicial replacement は Kan 複体。
方針：係数値との標準同型でホーンを移し、充填を全空間へ戻す。
規約：指定した対象 c の係数値にのみ Kan 性を要求する。
使われ方：Kerodon Theorem 5.3.5.7、長さ零の帰納段階での全空間の構造。 -/
lemma simplicialReplacementPoint_kanComplex
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (simplicialReplacement F) := by
  let e := asIso (simplicialReplacementConstantLift F c)
  apply kanComplex_of_rightHornFillers
  intro n i _ a
  obtain ⟨H, hH⟩ := KanComplex.hornFilling (a ≫ e.inv)
  refine ⟨H ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：一点の薄い圏上の left scaffold は全空間の前合成の同値条件を満たす。
方針：係数値からの同型と fiber からの同型の間の比較を、fiber 比較の同値へ帰着する。
規約：結論は任意の quasicategory を標的とする前合成の同値性。
使われ方：Kerodon Theorem 5.3.5.7、有限順序上の scaffold 比較の初期条件。 -/
lemma IsLeftScaffold.isPrecompositionEquivalence_of_point
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    {E : SSet.{u}} {p : E ⟶ nerve C} [LeftFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l) (c : C) :
    IsPrecompositionEquivalence l := by
  have := simplicialReplacementPoint_kanComplex F c
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : IsIso (vertexFiberι p (nerveVertex c)) := vertexFiberι_isIso_of_nervePoint p c
  rcases hs with ⟨h, hf⟩
  have hc : simplicialReplacementConstantLift F c ≫ l =
      leftScaffoldFiberMap p F l h c ≫ vertexFiberι p (nerveVertex c) := rfl
  have he : IsQCatEquivalence (simplicialReplacementConstantLift F c ≫ l) := by
    rw [hc]
    exact (hf c).comp
      (qCatEquivalenceOfIso (asIso (vertexFiberι p (nerveVertex c)))).isQCatEquivalence
  exact ((qCatEquivalenceOfIso (asIso (simplicialReplacementConstantLift F c))).isQCatEquivalence
    |>.cancel_left he).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
