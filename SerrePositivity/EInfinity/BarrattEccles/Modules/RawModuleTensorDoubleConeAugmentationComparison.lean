module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeOverColumn
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementAugmentationJoin
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeSliceTriangle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt

/-!
概要：同じ全 slice 評価と元の通常 augmentation 円柱を指定導来源で比較する。
方針：全標準単体の同じ終端付き列から join を照合し、同じ実分解を後合成する。
規約：HA Construction 1.3.1.13、元の全実写像 h を保持する。
使われ方：元の全 augmentation 同型の逆と同じ評価屋根の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeOverDiagram_uncurry :
    sliceOverUncurry (strictRawModuleTensorDoubleConeOverDiagram A X P Q) =
      strictRawModuleTensorElementAugmentationJoin A X P Q := by
  apply join_left_hom_ext
  · rw [sliceOverUncurry_fixed, strictRawModuleTensorElementAugmentationJoin_inr]
  · intro n a
    obtain ⟨c, rfl⟩ := (SSet.yonedaEquiv (X := nerve
      (strictRawModuleTensorElementIndex A X P Q))).symm.surjective a
    rw [← sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp,
      sliceOverUncurry_yoneda, strictRawModuleTensorDoubleConeOverDiagram_app]
    exact (strictRawModuleTensorElementAugmentationJoin_restrict_simplex A X P Q c).symm

lemma strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h_source :
    (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q).h ≫
      moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) =
    (strictRawModuleDiagramNatTransHomotopy A X
      (strictRawModuleTensorElementAugmentation A X P Q)).h := by
  let K := nerve (strictRawModuleTensorElementIndex A X P Q)
  let T := dgModuleNerve A (dgAlgebraCategory A ((assocForget A).obj X))
  let R := moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X))
  have hp : (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy A X P Q).h ≫ R =
      (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫
        sliceOverUncurry (strictRawModuleTensorDoubleConeOverDiagram A X P Q) ≫ R := by
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ R) (strictRawModuleTensorDoubleConeSliceEvaluationHomotopy_h A X P Q)
  have hj := congrArg (fun j : join K (Δ[0] : SSet.{u + 1}) ⟶ T =>
    (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ rightMappingSpacePrism K ≫ j ≫ R)
    (strictRawModuleTensorDoubleConeOverDiagram_uncurry A X P Q)
  exact hp.trans (hj.trans (strictRawModuleTensorElementAugmentationJoin_prism_source A X P Q))

end SerrePositivity.EInfinity.BarrattEccles
