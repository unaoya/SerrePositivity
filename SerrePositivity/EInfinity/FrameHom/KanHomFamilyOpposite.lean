module
public import SerrePositivity.EInfinity.FrameHom.KanHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OppositeWeakHomotopy

/-!
概要：同じ底全体でEx∞係数の反転を比較する。
方針：元のEx∞単位とその反転を、既存のKan係数のedgewise比較へつなぐ。
規約：反転するのは値であり、底とその全射はそのまま保つ。
使われ方：全要素圏と元の反対要素圏の係数規約の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.SimplicialModel

/-- 元のEx∞単位の弱同値性を同じ射で記録する。 -/
lemma kanHomFamilyUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (exInfinityUnit.app X) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SSet.anodyneExtensions.Q_inverts _ (exInfinityUnit_anodyne X))

/-- 同じKan値の図式に元のEx∞単位を適用した全関手同型。 -/
def kanDiagramExInfinityUnitIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (kanHomFamilyCoherent (F ⋙ kanObjectForget)) := by
  have : ∀ c, KanComplex ((F ⋙ kanObjectForget).obj c) := fun c => (F.obj c).isKanComplex
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨F, trivial⟩) (G := ⟨kanHomFamily (F ⋙ kanObjectForget), trivial⟩)
    (Functor.whiskerLeft (F ⋙ kanObjectForget) exInfinityUnit)
    (fun c => by
      have : KanComplex (F.obj c).obj := (F.obj c).isKanComplex
      have : KanComplex ((𝟭 SSet).obj (F.obj c).obj) := (F.obj c).isKanComplex
      have : Quasicategory ((𝟭 SSet).obj (F.obj c).obj) := inferInstance
      change IsQCatEquivalence (exInfinityUnit.app (F.obj c).obj)
      exact (kanHomFamilyUnit_isWeakHomotopyEquivalence _).isSimplicialHomotopyEquivalence.isQCatEquivalence)

/-- 元のEx∞単位の反転を同じ全図式の自然変換として記録する。 -/
def kanHomFamilyOppositeUnit {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    F ⋙ SSet.opFunctor ⟶ (kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget :=
  Functor.whiskerRight (Functor.whiskerLeft F exInfinityUnit) SSet.opFunctor

/-- 同じ底の全図式で、元の係数の反転とKan化を既存の単位で比較する。 -/
def kanHomFamilyOppositeUnitIso {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)) := by
  let G := (kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget
  let η : F ⋙ SSet.opFunctor ⟶ G := kanHomFamilyOppositeUnit F
  have hη : ∀ c, IsWeakHomotopyEquivalence (η.app c) := by
    intro c
    change IsWeakHomotopyEquivalence (SSet.opFunctor.map (exInfinityUnit.app (F.obj c)))
    exact SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence
      (exInfinityUnit.app (F.obj c)) (kanHomFamilyUnit_isWeakHomotopyEquivalence _)
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨kanHomFamily (F ⋙ SSet.opFunctor), trivial⟩)
    (G := ⟨kanHomFamily G, trivial⟩)
    (kanHomFamilyMap η)
    (fun c => kanHomFamilyMap_isQCatEquivalence η hη c)

/-- Kan化した全係数と、値だけを反転してKan化した全係数の関手同型。 -/
def kanHomFamilyOppositeComparisonIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent F)
      (kanHomFamilyCoherent (F ⋙ SSet.opFunctor)) :=
  (kanDiagramOppositeComparisonIso (kanHomFamily F)).trans
    ((kanDiagramExInfinityUnitIso (kanHomFamily F ⋙ kanObjectOpFunctor)).trans
      (kanHomFamilyOppositeUnitIso F).symm)
end SerrePositivity.EInfinity.FrameHom
