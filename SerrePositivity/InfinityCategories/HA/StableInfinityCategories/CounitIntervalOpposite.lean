module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorOppositeEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.IntervalFunctorOpposite
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison
/-!
概要：実余単位の標準区間比較から反対側の指定単位条件を得る。
方針：同じ実ホモトピーを反転し、任意パラメータ族の合成表示で比較する。
規約：標準の写像空間比較と元の全関手を保持する。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 同じ実余単位の反転が与える h Fun の指定単位。 -/
def counitOppositeUnitHom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 Y.op) (opFunctor.map G ≫ opFunctor.map F) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv (G ≫ F) (𝟙 Y)
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))

/-- 反転した指定単位の成分は、元の同じ余単位成分の反対。 -/
lemma counitOppositeUnitHom_component {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (counitOppositeUnitHom H) (SSet.opObjEquiv.symm y) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent counitOppositeUnitHom
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorOppositeHomEquiv_evaluate, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyCategoryOpHomEquiv_homMk]
  rfl

/-- 元の余単位の標準区間比較の反転は、反対側の指定単位比較とホモトピック。 -/
lemma counitIntervalReverse_homotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y)) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
            (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated)))
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso x (G.app (Opposite.op ⦋0⦌) y)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap (counitOppositeUnitHom H) (SSet.opObjEquiv.symm y)
          (SSet.opObjEquiv.symm x))) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated
  let m := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y)
  obtain ⟨K⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalReverseFamily_postcompose_hom
    (F.app (Opposite.op ⦋0⦌) x) e
  let K' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp K (opFunctor.map m)
  refine ⟨{ h := K'.h, h₀ := K'.h₀.trans ?_, h₁ := K'.h₁.trans ?_, rel := K'.rel }⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalReverseFamily_precomp m _).symm
  · change opFunctor.map m ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso
      (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) (G.app (Opposite.op ⦋0⦌) y))).hom ≫ _ = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso_naturality]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap, counitOppositeUnitHom_component]
    rfl

/-- 同じ余単位の全区間比較の同値性から、反対側の標準単位条件を得る。 -/
lemma counitOppositeUnitHom_mappingSpaceCondition {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x (G.app (Opposite.op ⦋0⦌) y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (counitOppositeUnitHom H) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval]
  intro y x
  let x' := SSet.opObjEquiv x
  let y' := SSet.opObjEquiv y
  let m := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x' (G.app (Opposite.op ⦋0⦌) y') ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x')
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y').toTruncated)
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op (h x' y').isQCatEquivalence
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso
    (F.app (Opposite.op ⦋0⦌) x') y')).isQCatEquivalence
  have hr := hm.comp hi
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (opFunctor.map m ≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso (F.app (Opposite.op ⦋0⦌) x') y').hom) at hr
  have he := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalReverseFamily_eq
    (F.app (Opposite.op ⦋0⦌) x') y' m
  rw [← he] at hr
  obtain ⟨K⟩ := counitIntervalReverse_homotopy H x' y'
  have ht := hr.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy K)
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalOppositeIso x'
    (G.app (Opposite.op ⦋0⦌) y'))).isQCatEquivalence.cancel_left ht).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
