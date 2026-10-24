module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationUnitTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedConstantIntervalFamilies
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
variable (A B : DGFunctorCommaObject R E E (DGFunctor.id E))
  (k : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
def dgGluingClosedAugmentationSquare : (Δ[1] : SSet.{max u v}) ⊗ Δ[1] ⟶ dgNerve R E :=
  (Δ[1] ◁ SSet.yonedaEquiv.symm (dgClosedEdge R Q k).edge) ≫
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E)
lemma dgGluingClosedAugmentationSquare_triangle (i : Fin 2) :
    squareTriangle i ≫ dgGluingClosedAugmentationSquare R E A B k =
      SSet.yonedaEquiv.symm (dgGluingClosedAugmentationTriangle R E A B k i) := by
  apply SSet.yonedaEquiv.injective
  have hcoords : SSet.yonedaEquiv (squareTriangle (0 : Fin 2)) =
      (stdSimplex.objEquiv.symm (SimplexCategory.σ (0 : Fin 2)),
        stdSimplex.objEquiv.symm (SimplexCategory.σ (1 : Fin 2))) := by
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  have hcoords' : SSet.yonedaEquiv (squareTriangle (1 : Fin 2)) =
      (stdSimplex.objEquiv.symm (SimplexCategory.σ (1 : Fin 2)),
        stdSimplex.objEquiv.symm (SimplexCategory.σ (0 : Fin 2))) := by
    apply Prod.ext
    all_goals apply SSet.stdSimplex.ext
    all_goals intro j; fin_cases j <;> rfl
  fin_cases i
  all_goals rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
  · change (dgGluingClosedAugmentationSquare R E A B k).app (Opposite.op ⦋2⦌)
      (SSet.yonedaEquiv (squareTriangle 0)) =
      dgGluingClosedAugmentationTriangle R E A B k 0
    erw [hcoords]
    change ((dgGluingClosedAugmentationTriangle R E A B k 0).map
      (dgUniverseLiftUp.{u, max u v, max u v} R E)).map
        (dgUniverseLiftDown.{u, max u v, max u v} R E) = _
    apply Simplex.ext
    change SimplexData.map (SimplexData.map _ _) _ = _
    rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]
  · change (dgGluingClosedAugmentationSquare R E A B k).app (Opposite.op ⦋2⦌)
      (SSet.yonedaEquiv (squareTriangle 1)) =
      dgGluingClosedAugmentationTriangle R E A B k 1
    erw [hcoords']
    change ((dgGluingClosedAugmentationTriangle R E A B k 1).map
      (dgUniverseLiftUp.{u, max u v, max u v} R E)).map
        (dgUniverseLiftDown.{u, max u v, max u v} R E) = _
    apply Simplex.ext
    change SimplexData.map (SimplexData.map _ _) _ = _
    rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]


def dgGluingSquareUnitCollapse (j : Fin 2) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  square_isPushout.desc (stdSimplex.σ j) (stdSimplex.σ j) rfl
lemma dgGluingSquareUnitCollapse_triangle (j i : Fin 2) :
    squareTriangle i ≫ dgGluingSquareUnitCollapse.{u} j = stdSimplex.σ j := by
  fin_cases i
  · exact square_isPushout.inl_desc _ _ _
  · exact square_isPushout.inr_desc _ _ _

private lemma dgGluingDegenerateTriangleYoneda (s : Simplex R E 1) (j : Fin 2) :
    stdSimplex.σ j ≫ SSet.yonedaEquiv.symm s =
      (SSet.yonedaEquiv (X := dgNerve R E)).symm (s.pullback (SimplexCategory.σ j).toOrderHom) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_σ_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl
variable (X : DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E X.source
lemma dgGluingNormalizationInAugmentationSquare_eq :
    dgGluingClosedAugmentationSquare R E NX X (dgGluingIdentityCommaNormalizationClosedIn R E X) =
      dgGluingSquareUnitCollapse.{max u v} 0 ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge := by
  apply square_isPushout.hom_ext
  · rw [dgGluingClosedAugmentationSquare_triangle,
      dgGluingNormalizationInAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
  · rw [dgGluingClosedAugmentationSquare_triangle,
      dgGluingNormalizationInAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
lemma dgGluingNormalizationOutAugmentationSquare_eq :
    dgGluingClosedAugmentationSquare R E X NY (dgGluingIdentityCommaNormalizationClosedOut R E X) =
      dgGluingSquareUnitCollapse.{max u v} 1 ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E X.augmentation).edge := by
  apply square_isPushout.hom_ext
  · rw [dgGluingClosedAugmentationSquare_triangle,
      dgGluingNormalizationOutAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]
  · rw [dgGluingClosedAugmentationSquare_triangle,
      dgGluingNormalizationOutAugmentationTriangle_eq,
      ← Category.assoc, dgGluingSquareUnitCollapse_triangle, dgGluingDegenerateTriangleYoneda]


lemma dgGluingClosedAugmentationSquare_constant_family {K : SSet.{max u v}} :
    (Δ[1] ◁ intervalMappingUncurry
      ((SSet.const (X := K) (pinchedClosedVertex R Q k)) ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
          (Simplex.vertex A) (Simplex.vertex B))) ≫
      dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
        dgNerve.map (dgUniverseLiftDown.{u, max u v, max u v} R E) =
    (Δ[1] ◁ CartesianMonoidalCategory.fst (Δ[1] : SSet.{max u v}) K) ≫
      dgGluingClosedAugmentationSquare R E A B k := by
  rw [dgGluingPinchedConstantIntervalFamily, pinchedClosedVertex_val,
    whiskerLeft_comp, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories
