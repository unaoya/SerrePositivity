module
public import SerrePositivity.KST.SConstruction.DGGluingAxesCofiberCells
public import SerrePositivity.KST.SConstruction.DGGluingAxesRepresentableComponents

/-! # 元の二軸二セルの Yoneda 像の厳密回収
概要：持ち上げた上下二セルの像を、元の実代表 cofiber の同じ二セルに同定する。
方針：元の閉零 cycle と同じ実零 Hom end における比較原始元の一意性を照合する。
規約：同じ三頂点・三辺・比較を保持。使われ方：実四角形全体の押し出し反映。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "A" => dgGluingRightAxisObject R C D M zc X.right
local notation "B" => dgGluingLeftAxisObject R C D M zd X.left
local notation "Z" => dgGluingRightAxisObject R C D M zc zd
local notation "F" => dgYoneda R G
local notation "s" => dgGluingAxesRepresentableCofiberData R C D M zc hc zd hd X

/-- 元の包含・射影を持つ実下側二セルは、同じ代表 cofiber の下側二セルを回収する。 -/
lemma dgGluingAxesCofiberLowerCell_yoneda :
    (dgGluingAxesCofiberLowerCell R C D M zc hc zd hd X).simplex.map (F) =
      (s).lowerTriangle := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle (F)
      (dgGluingAxisRightInclusion R C D M zc hc X))
  · apply heq_of_eq
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle (F)
      (dgGluingAxisLeftProjection R C D M zd hd X)).trans
        (congrArg (fun k => (closedHomEquiv R (RightModule R G)
            (ForgetEnrichment.of (Complex R) (representable R X))
            (ForgetEnrichment.of (Complex R) (representable R B)) k).val)
          (dgGluingAxesRepresentable_right R C D M zc hc zd hd X).symm)
  · apply heq_of_eq
    exact (dgGluingAxesYonedaHom_subsingleton R C D M zc hc zd hd X 0).elim _ _
  · apply heq_of_eq
    exact (dgGluingAxesYonedaHom_subsingleton R C D M zc hc zd hd X (-1)).elim _ _

/-- 指定零対象を経由する実上側二セルも、同じ代表 cofiber の上側二セルを回収する。 -/
lemma dgGluingAxesCofiberUpperCell_yoneda :
    (dgGluingAxesCofiberUpperCell R C D M zc hc zd hd X).simplex.map (F) =
      (s).upperTriangle := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle (F) (0 : ForgetEnrichment.of (Complex R) A ⟶
      ForgetEnrichment.of (Complex R) Z)).trans
        (congrArg (fun k => (closedHomEquiv R (RightModule R G)
            (ForgetEnrichment.of (Complex R) (representable R A))
            (ForgetEnrichment.of (Complex R) (representable R Z)) k).val)
          (dgGluingAxesRepresentable_left R C D M zc hc zd hd X).symm)
  · apply heq_of_eq
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle (F) (0 : ForgetEnrichment.of (Complex R) Z ⟶
      ForgetEnrichment.of (Complex R) B)).trans
        (congrArg (fun k => (closedHomEquiv R (RightModule R G)
            (ForgetEnrichment.of (Complex R) (representable R Z))
            (ForgetEnrichment.of (Complex R) (representable R B)) k).val)
          (dgGluingAxesRepresentable_top R C D M zc hc zd hd X).symm)
  · apply heq_of_eq
    exact (dgGluingAxesYonedaHom_subsingleton R C D M zc hc zd hd X 0).elim _ _
  · apply heq_of_eq
    exact (dgGluingAxesYonedaHom_subsingleton R C D M zc hc zd hd X (-1)).elim _ _

end SerrePositivity.KST.SConstruction
