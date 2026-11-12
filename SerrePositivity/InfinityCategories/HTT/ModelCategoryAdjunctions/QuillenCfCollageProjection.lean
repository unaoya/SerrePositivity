module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentThinNerveMap
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInclusions
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration

/-!
概要：元の cf 単体的対応圏の区間への射影と両側の包含との厳密な両立。
方針：二段の通常の関手を coherent nerve 上へ延長し、薄い標的の頂点で比較する。
規約：局所 Kan 性は元の固定 SM7 と Quillen 条件から得る。
使われ方：HTT 5.2.4.6、Cartesian・coCartesian な持ち上げを構成するための底。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
open _root_.SerrePositivity.KST.SConstruction

/-- 下段を零、上段を一へ送る元の cf 対応圏の通常の関手。 -/
def quillenCfCollageLevelFunctor : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R ⥤ ULift.{max u v} (Fin 2) where
  obj X := match X.obj with
    | .inl _ => ULift.up 0
    | .inr _ => ULift.up 1
  map {X Y} f := by
    rcases X with ⟨X, hX⟩
    rcases Y with ⟨Y, hY⟩
    rcases X with X | X <;> rcases Y with Y | Y
    · exact 𝟙 _
    · exact homOfLE (by decide : (ULift.up (0 : Fin 2) : ULift.{max u v} _) ≤ ULift.up 1)
    · exact isEmptyElim (SSet.unitHomEquiv enrichedCollageEmpty f.hom)
    · exact 𝟙 _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 同じ二段関手から、持ち上げた二点鎖の nerve への全次数の射を作る。 -/
def quillenCfCollageNerveLevel : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R ⟶
    nerve (ULift.{max u v} (Fin 2)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentThinNerveMap (quillenCfCollageLevelFunctor R)


/-- 元の cf 対応圏の coherent nerve から標準区間への射影。 -/
def quillenCfCollageProjection : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R ⟶
    (Δ[1] : SSet.{max u v}) :=
  quillenCfCollageNerveLevel R ≫ (stdSimplex.isoNerve 1).inv


/-- 射影は下段の元の頂点を零、上段の元の頂点を一へ送る。 -/
lemma quillenCfCollageProjection_vertex (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R) :
    (quillenCfCollageProjection R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      stdSimplex.obj₀Equiv.symm (match X.obj with
        | .inl _ => (0 : Fin 2)
        | .inr _ => 1) := by
  change (stdSimplex.isoNerve 1).inv.app _
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentThinNerveMap (quillenCfCollageLevelFunctor R)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentThinNerveMap_vertex]
  rcases X with ⟨X, hX⟩
  rcases X with X | X <;> rfl

/-- 下段の cf nerve の包含は、二点鎖の零頂点の上にある。 -/
lemma quillenCfCollageBottom_level :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ≫ quillenCfCollageNerveLevel R =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin 2))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x]
  change (quillenCfCollageNerveLevel R).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentThinNerveMap_vertex _ _

/-- 上段の cf nerve の包含は、二点鎖の一頂点の上にある。 -/
lemma quillenCfCollageTop_level :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ≫ quillenCfCollageNerveLevel R =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (1 : Fin 2))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x]
  change (quillenCfCollageNerveLevel R).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentThinNerveMap_vertex _ _

variable {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]
include adj SC SD in
/-- 固定 SM7 と元の Quillen 条件の下で、同じ区間射影は inner fibration。 -/
lemma quillenCfCollageProjection_innerFibration :
    InnerFibration (quillenCfCollageProjection R) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageInfinity_quasicategory R adj SC SD
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.stdSimplexTarget_innerFibration 1 _

/-- 元の下段包含と区間射影の合成は零頂点への定値射に一致する。 -/
lemma quillenCfCollageBottom_projection :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ≫ quillenCfCollageProjection R =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ≫
    (quillenCfCollageNerveLevel R ≫ (stdSimplex.isoNerve 1).inv) = _
  rw [← Category.assoc, quillenCfCollageBottom_level]
  rfl

/-- 元の上段包含と区間射影の合成は一頂点への定値射に一致する。 -/
lemma quillenCfCollageTop_projection :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ≫ quillenCfCollageProjection R =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ≫
    (quillenCfCollageNerveLevel R ≫ (stdSimplex.isoNerve 1).inv) = _
  rw [← Category.assoc, quillenCfCollageTop_level]
  rfl

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
