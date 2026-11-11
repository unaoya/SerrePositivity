module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputTriangleEvaluations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputDiagonals
/-!
概要：元入力付き四補正道の対角を、同じ実三角形の対角評価へ戻す。
方針：合成対応の対角評価と uncurry の自然性を使う。
規約：全時間と元入力を保持する。使われ方：共有四面体の六片の端点固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetFirstInputTriangleEvaluation_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstRestrictedTriangleEvaluation_diagonal
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetLastInputTriangleEvaluation_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastRestrictedTriangleEvaluation_diagonal (Z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetPreNormalizationInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetFirstInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingHomTargetPreCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetFirstInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingHomTargetExitCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetLastInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingHomTargetExitCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetLastInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
