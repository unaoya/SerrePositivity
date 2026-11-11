module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleTriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 全 Hom end の二つの三角形による実加群四角形

概要：四辺・対角・二つの次数 −1 成分を持つ dg 加群四角形を実単体写像にする。
方針：共通の対角を持つ合成三角形を正方形の二セル表示で貼る。
規約：通常の dg 自然性を全次数で保持。使われ方：実 cone 四角形の関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 全 dg 自然なホモトピーを指定した加群の四角形。 -/
@[ext] structure DGModuleSquareData (W X Y Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D) where
  bottom : W ⟶ X
  left : W ⟶ Y
  right : X ⟶ Z
  top : Y ⟶ Z
  diagonal : W ⟶ Z
  lowerHomotopy : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z) (-1)
  upperHomotopy : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z) (-1)
  lowerEquation : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).d (-1) 0 lowerHomotopy =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (bottom ≫ right))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) diagonal)).val
  upperEquation : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).d (-1) 0 upperHomotopy =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (left ≫ top))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) diagonal)).val

namespace DGModuleSquareData
variable {A D} {W X Y Z T : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (s : DGModuleSquareData A D W X Y Z)

/-- 四角形の下側の実二単体。 -/
def lowerTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).simplex

/-- 四角形の上側の実二単体。 -/
def upperTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation).simplex

/-- 二つの三角形は実際の対角で一致する。 -/
lemma triangles_compatible :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ (SSet.yonedaEquiv.symm s.upperTriangle :
      (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) =
    SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.lowerTriangle := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₁.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₁.symm)

/-- 二つの実三角形を貼った単体的四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm s.upperTriangle)
    (SSet.yonedaEquiv.symm s.lowerTriangle) s.triangles_compatible

/-- 下側セルへの制限。 -/
lemma square_lower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ s.square = SSet.yonedaEquiv.symm s.lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 上側セルへの制限。 -/
lemma square_upper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ s.square = SSet.yonedaEquiv.symm s.upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 終点と二つのホモトピーを閉零加群射で後合成する。 -/
def postcompose (q : Z ⟶ T) : DGModuleSquareData A D W X Y T where
  bottom := s.bottom
  left := s.left
  right := s.right ≫ q
  top := s.top ≫ q
  diagonal := s.diagonal ≫ q
  lowerHomotopy := _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val
    s.lowerHomotopy (add_zero (-1))
  upperHomotopy := _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) q)).val
    s.upperHomotopy (add_zero (-1))
  lowerEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_postcompose_differential A D _ _ _ _ s.lowerEquation q
  upperEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangle_postcompose_differential A D _ _ _ _ s.upperEquation q

end DGModuleSquareData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
