module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionSecondUnitDiagram
public import SerrePositivity.InfinityCategories.Derived.Gluing.SecondUnitSquareGeometry
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionSquareEvaluation
/-!
概要：第二閉恒等入力の標準合成正方形を最大時刻による元の区間族へ同定する。
方針：全 slice 図式の表示を右 join prism で評価し、二つの切断の合成を計算する。
規約：Small 仮定なしで同じ coherent prism・全時間・元 Hom 入力を保持する。
使われ方：同じ正方形の標準三角形への制限から第二単位面の厳密退化を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingDGCompositionSecondUnitSquare {K : SSet.{max u v}} {x y : E}
    (f : K ⟶ DGNerve.pinchedHom R E x y) :
    rightMappingSpacePrism (Δ[1] ⊗ K) ≫ sliceOverUncurry
      (dgPinchedCompositionFamilyPrism R E f
        (SSet.const (pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y))))) =
    (α_ Δ[1] Δ[1] K).inv ≫ (dgGluingUnitSquareMax ▷ K) ≫
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t, k⟩
  change (sliceOverUncurry _).app (Opposite.op ⦋n⦌)
    ((rightMappingSpacePrism (Δ[1] ⊗ K)).app _ (s, (t, k))) = _
  rw [rightMappingSpacePrism_evaluate, sliceOverUncurry_simplex_coordinate,
    dgGluingDGCompositionFamilyPrism_second_unit_diagram,
    Iso.inv_hom_id_assoc, ← SSet.yonedaEquiv_naturality,
    Equiv.apply_symm_apply]
  change (dgNerve R E).map
    (SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv s).toOrderHom)).op
    ((dgNerve R E).map
      (SimplexCategory.mkHom (dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op
      (f.app _ k).val) =
    (intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _)).app _
      ((dgGluingUnitSquareMax.app _ (s, t)), k)
  rw [pinchedHomToIntervalMappingSpace_evaluate, ← types_comp_apply, ← Functor.map_comp]
  congr 2
  apply congrArg (dgNerve R E).map
  change (SimplexCategory.mkHom ((dgCompositionUnitCollapse
    (stdSimplex.objEquiv t).toOrderHom).comp
      (coherentPrismCut (stdSimplex.objEquiv s).toOrderHom))).op = _
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun h : Fin (n + 1) →o Fin (n + 2) => h i)
    (dgGluingSecondUnit_prism_cut (stdSimplex.objEquiv s).toOrderHom
      (stdSimplex.objEquiv t).toOrderHom)
end SerrePositivity.InfinityCategories
