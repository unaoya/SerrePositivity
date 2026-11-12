module
public import SerrePositivity.KST.ProExcision.Lemma416Functoriality
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# 次数ごとの群の nerve と対角 bar の成分比較

概要：単体的群の分類空間の対角の写像を、係数方向と nerve 方向の二つの写像に分ける。
方針：既存の monoidBar の uncurry の実定義と自由化関手の合成保存を使う。
規約：KST App. A・Lemma 4.16 の単体環への移送。H_* の新しい模型を作らない。
使われ方：次数ごとに自然な実 m 次ホモトピーの対角への制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：単体的群の既存の対角分類空間。
方針：群からモノイドへの忘却後に既存の monoidBar を使う。
規約：KST App. A の B H。使われ方：次数ごとの実比較の対角の始域と値域。 -/
abbrev simplicialGroupBar (M : SimplicialObject GrpCat.{u}) : SSet.{u} :=
  monoidBar (M ⋙ forget₂ GrpCat MonCat)

/-- 概要：単体的群の写像の既存の対角分類空間の射。
方針：忘却と既存の monoidBarMap を合成する。
規約：KST App. A。使われ方：実群準同型 φ の単体版の端点。 -/
def simplicialGroupBarMap {M N : SimplicialObject GrpCat.{u}} (f : M ⟶ N) :
    simplicialGroupBar M ⟶ simplicialGroupBar N :=
  monoidBarMap (Functor.whiskerRight f (forget₂ GrpCat MonCat))

/-- 概要：対角 bar の自由化した面・退化は係数方向と nerve 方向に分かれる。
方針：uncurry の射の定義を自由化の合成保存へ渡す。
規約：KST 4.16、二つの次数を混同しない対角模型。
使われ方：自然な実区間射の対角の単体性の証明。 -/
lemma linearizedGroupBar_map_decomposition (M : SimplicialObject GrpCat.{u})
    {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (simplicialGroupBar M)).map φ =
      (groupLinearizedMap (M.map φ).hom).app k ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj (M.obj l)))).map φ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map
      (((nerveMap (SingleObj.mapHom _ _ (M.map φ).hom)).app k) ≫
        (nerve (SingleObj (M.obj l))).map φ) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map_comp _ _

/-- 概要：対角の線形区間の面・退化も係数方向と nerve 方向に分かれる。
方針：前半の自由化した分解と整数テンソルの合成則を使う。
規約：KST 4.16、区間の単体方向は nerve 側の後半で変える。
使われ方：次数ごとのホモトピーから対角の実区間射を構成する。 -/
lemma linearizedGroupBar_cylinder_decomposition (M : SimplicialObject GrpCat.{u})
    {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (simplicialGroupBar M)).map φ =
      (linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ (M.map φ).hom))).app k ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (nerve (SingleObj (M.obj l)))).map φ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (simplicialGroupBar M)).map φ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).map φ) = _
  rw [linearizedGroupBar_map_decomposition]
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp ((groupLinearizedMap (M.map φ).hom).app k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (nerve (SingleObj (M.obj l)))).map φ)
    (𝟙 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).obj k)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).map φ)
  simp only [Category.id_comp] at ht
  exact ht

end SerrePositivity.KST.ProExcision
