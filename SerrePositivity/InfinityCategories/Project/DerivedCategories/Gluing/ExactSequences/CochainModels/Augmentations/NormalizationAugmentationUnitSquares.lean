module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.NormalizationAugmentationUnitTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PinchedConstantIntervalFamilies
/-! # 標準正規化側面の実正方形

概要：標準閉射の augmentation 正方形を、元 augmentation と単位貼り合わせの合成へ同定する。
方針：二つの生成三角形へ制限し、正方形の pushout の一意性を使う。
規約：一般パラメーターの定値閉射族を含め、対象の Small 性を要求しない。
使われ方：固定辺を保つ三角形族の側面補正を厳密に回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
variable (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  (k : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) A ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) B)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
def dgGluingClosedAugmentationSquare : (Δ[1] : SSet.{max u v}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  (Δ[1] ◁ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q k).edge) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)
lemma dgGluingClosedAugmentationSquare_triangle (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ dgGluingClosedAugmentationSquare R E A B k =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k i) := by
  apply SSet.yonedaEquiv.injective
  have hcoords : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2)) =
      (stdSimplex.objEquiv.symm (SimplexCategory.σ (0 : Fin 2)),
        stdSimplex.objEquiv.symm (SimplexCategory.σ (1 : Fin 2))) := by
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  have hcoords' : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (1 : Fin 2)) =
      (stdSimplex.objEquiv.symm (SimplexCategory.σ (1 : Fin 2)),
        stdSimplex.objEquiv.symm (SimplexCategory.σ (0 : Fin 2))) := by
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  fin_cases i
  all_goals rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
  · change (dgGluingClosedAugmentationSquare R E A B k).app (Opposite.op ⦋2⦌)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 0
    erw [hcoords]
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max u v, max u v} R E)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E) = _
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map _ _) _ = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id]
  · change (dgGluingClosedAugmentationSquare R E A B k).app (Opposite.op ⦋2⦌)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 1
    erw [hcoords']
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E A B k 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max u v, max u v} R E)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E) = _
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map _ _) _ = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id]


def dgGluingSquareUnitCollapse (j : Fin 2) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (stdSimplex.σ j) (stdSimplex.σ j) rfl
lemma dgGluingSquareUnitCollapse_triangle (j i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ dgGluingSquareUnitCollapse.{u} j = stdSimplex.σ j := by
  fin_cases i
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

private lemma dgGluingDegenerateTriangleYoneda (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) (j : Fin 2) :
    stdSimplex.σ j ≫ SSet.yonedaEquiv.symm s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (s.pullback (SimplexCategory.σ j).toOrderHom) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_σ_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source
lemma dgGluingNormalizationInAugmentationSquare_eq :
    dgGluingClosedAugmentationSquare R E NX X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) =
      dgGluingSquareUnitCollapse.{max u v} 0 ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [dgGluingClosedAugmentationSquare_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationInAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
  · rw [dgGluingClosedAugmentationSquare_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationInAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
lemma dgGluingNormalizationOutAugmentationSquare_eq :
    dgGluingClosedAugmentationSquare R E X NY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X) =
      dgGluingSquareUnitCollapse.{max u v} 1 ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
  · rw [dgGluingClosedAugmentationSquare_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationOutAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
  · rw [dgGluingClosedAugmentationSquare_triangle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationOutAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]


lemma dgGluingClosedAugmentationSquare_constant_family {K : SSet.{max u v}} :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      ((SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Q k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex B))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E) =
    (Δ[1] ◁ CartesianMonoidalCategory.fst (Δ[1] : SSet.{max u v}) K) ≫
      dgGluingClosedAugmentationSquare R E A B k := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedConstantIntervalFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex_val,
    whiskerLeft_comp, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
