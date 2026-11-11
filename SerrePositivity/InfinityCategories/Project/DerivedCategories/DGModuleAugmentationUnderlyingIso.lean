module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnderlyingSpaceQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationClosedEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy
/-!
概要：実分解圏上の同じ augmentation を、空間値全関手の比較同型へ昇格する。
方針：同じ実頂点辺の準同型性から像の可逆性を示し、全単体ホモトピー自身から同型を作る。
規約：半自由 Hom の始域と同じ共通対象宇宙を使い、元の出力に射影性を課さない。
使われ方：実 D(R) 値 Hom の augmentation の空間値比較同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}))
/-- 同じ実 augmentation の全単体族を、R からの基礎空間関手へ送ったホモトピー。 -/
def dgModuleAugmentationUnderlyingSpaceHomotopy :
    SSet.Homotopy
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift R C PUnit.{1} F)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift R C PUnit.{1} F)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftHomotopy.{max (u + 1) v, max (u + 1) v + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C PUnit.{1} F)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C)
/-- 同じ空間値ホモトピーの実頂点辺は、元の同じ実辺を持ち上げて写したもの。 -/
lemma dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_edge
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C PUnit.{1} F) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C).app (Opposite.op ⦋1⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C PUnit.{1} F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge) := rfl
/-- 同じ空間値 augmentation の全ての実頂点成分は可逆。 -/
lemma dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_isInvertible
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C PUnit.{1} F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).toTruncated := by
  let e := (SSet.Edge.ofTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
          (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1})).onClosed.map X.augmentation)))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C)
  have hInv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity_invertsQuasiIso R C X.augmentation X.quasiIso
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge = e.edge := by
    rw [dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_edge,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy_vertex_edge]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (dgModuleAugmentationUnderlyingSpaceHomotopy R C F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).toTruncated) (f := e.toTruncated) he).mpr hInv
/-- 同じ実 augmentation の全単体族が与える、分解圏上の空間値全関手の比較同型。 -/
def dgModuleAugmentationUnderlyingSpaceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift R C PUnit.{1} F)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C)
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift R C PUnit.{1} F)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (dgModuleAugmentationUnderlyingSpaceHomotopy R C F) (by
    rintro ⟨s⟩
    obtain ⟨X, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R)
      (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C PUnit.{1} F)).symm.surjective s
    exact dgModuleAugmentationUnderlyingSpaceHomotopy_vertex_isInvertible R C F X)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
