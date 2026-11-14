module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization

/-!
概要：元のstrict BE余単体図式を、同じobjectwise擬同型で局所化する。
方針：既存edgeLocalizationを元の通常nerveの指定辺集合に適用。
規約：IS-W2 R05の証明分割。任意coherent BE図式の厳密化は主張しない。
使われ方：同じ全評価・Tot頂点・U比較の局所化への輸送の源。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 元のstrict BE余単体図式の全通常nerve。 -/
abbrev StrictBETotDiagramNerve : SSet.{u+1} :=
  nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)

/-- 元の全自然変換の各成分が擬同型である、指定辺の集合。 -/
def strictBETotDiagramWeakEdges : Set ((StrictBETotDiagramNerve A) _⦋1⦌) :=
  {s | ∀ j, QuasiIso ((s.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).app j).hom}

/-- 一辺の指定条件は元の同じ全成分の擬同型性。 -/
theorem strictBETotDiagramWeakEdges_mk₁
    {F G : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ComposableArrows.mk₁ f ∈ strictBETotDiagramWeakEdges A ↔
      ∀ j, QuasiIso (f.app j).hom := Iff.rfl

/-- 元のstrict BE図式の指定objectwise擬同型の∞局所化。 -/
def StrictBETotDiagramInfinity : SSet.{u+1} :=
  edgeLocalization (StrictBETotDiagramNerve A) (strictBETotDiagramWeakEdges A)

instance strictBETotDiagramInfinity_quasicategory :
    Quasicategory (StrictBETotDiagramInfinity A) := edgeLocalization_quasicategory _ _

/-- 元の全strict図式のnerveからの指定局所化写像。 -/
def strictBETotDiagramLocalization :
    StrictBETotDiagramNerve A ⟶ StrictBETotDiagramInfinity A := edgeLocalizationMap _ _

/-- 同じ指定写像の全関手圏の普遍性。 -/
theorem strictBETotDiagramLocalization_isLocalization :
    IsLocalization (strictBETotDiagramLocalization A) (strictBETotDiagramWeakEdges A) :=
  edgeLocalization_isLocalization _ _

end SerrePositivity.EInfinity.BarrattEccles
