module
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalStageSupply
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentActionInput
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.SphereConeData

/-!
概要：新しい段提供者の全厳密 dg 射へ、D-S の同じ sphere cone の実射データを代入する。
方針：提供者の定義上の cone 等号で移送し、元の平坦分解・商射を保持する。
規約：全単体 map・厳密 vertex・edgeIso の存在は主張しない。型変更はしない。
使われ方：K-7 c4 の data 欄の無条件化と、到着する map・edgeIso の消費入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
local notation "s" => dgKappaUnconditionalStageProvider R κ hκ

/-- 新しい同じ段提供者の任意の厳密射に対する実懸垂データ。 -/
def dgKappaUnconditionalSuspensionMapData
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    DGKappaSuspensionMapData R A B (s A).cone (s B).cone :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionMapData R A B (perfDGInputHomEquiv R A B f) κ hκ

/-- data の実 cone 関手は、D-3 の元の全 Hom 共役関手そのもの。 -/
theorem dgKappaUnconditionalSuspensionMapData_cone
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    (dgKappaUnconditionalSuspensionMapData R κ hκ f).cone =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R A B (perfDGInputHomEquiv R A B f)
        hκ Fact.out := rfl

/-- 新提供者の元の perfect 集合を、同じ実射データが保存する。 -/
theorem dgKappaUnconditionalSuspensionMapData_preservesPerfect
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)
    (M : DGKappaCone R A (s A).cone)
    (hM : M ∈ dgKappaConePerfectObjects R A (s A).cone) :
    (dgKappaUnconditionalSuspensionMapData R κ hκ f).cone.obj M ∈
      dgKappaConePerfectObjects R B (s B).cone :=
  (dgKappaUnconditionalSuspensionMapData R κ hκ f).preservesPerfect M hM

/-- 供給された実射は、D-S の同じ平坦分解と実商への入力射と厳密に一致する。 -/
theorem dgKappaUnconditionalSuspensionInputMap_eq
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    dgKappaSuspensionInputMap R A B (s A).cone (s B).cone
        (dgKappaUnconditionalSuspensionMapData R κ hκ f) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B (perfDGInputHomEquiv R A B f) κ hκ := rfl

/-- map・厳密 vertex・端点固定 edgeIso のみが届けば、data は実供給で埋まる。 -/
def dgSuspensionUnconditionalCoherentActionOfMap
    (m : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R)
    (hv : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
      m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone))
    (he : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R s m hv f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone
            (dgKappaUnconditionalSuspensionMapData R κ hκ f))))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s where
  map := m
  vertex := hv
  data := dgKappaUnconditionalSuspensionMapData R κ hκ
  edgeIso := he

end SerrePositivity.KST.NonConnective
