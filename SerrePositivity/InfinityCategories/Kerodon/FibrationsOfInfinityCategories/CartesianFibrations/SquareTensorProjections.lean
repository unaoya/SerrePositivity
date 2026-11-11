module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareTensorIso

/-!
概要：積上の四角形の currying 同型は両射影を厳密に保持する。
方針：引き戻しの保存同型と二つの lift の射影を計算する。
規約：底側と全空間側を同時に保持する。
使われ方：表現条件の各パラメーターでの比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：四角形の currying は全空間側の射の内部 currying を回収する。
方針：引き戻し保存の逆射の第一射影と lift の第一射影を使う。
規約：全高次パラメーターの厳密な等式。
使われ方：pointed space への写像の各パラメーターでの評価。 -/
lemma transportSquareTensorIso_hom_pointed {E B : SSet.{u + 1}}
    (p : E ⟶ B) (K : SSet.{u + 1}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p K).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K) ≫ (ihomCurryIso E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram]
  rw [Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst]

/-- 概要：四角形の currying は底側の分類図式の内部 currying を回収する。
方針：引き戻し保存の逆射の第二射影と lift の第二射影を使う。
規約：分類図式を取り替えない。
使われ方：分類区間の各パラメーターでの評価。 -/
lemma transportSquareTensorIso_hom_diagram {E B : SSet.{u + 1}}
    (p : E ⟶ B) (K : SSet.{u + 1}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p K).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K) ≫ (ihomCurryIso B K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).hom := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram]
  rw [Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]

/-- 概要：四角形の uncurrying の全空間側は元の内部 uncurrying。
方針：順方向の射影公式から二つの同型を消去する。
規約：全高次パラメーターで成立する。
使われ方：四角形空間への族を積上へ戻す計算。 -/
lemma transportSquareTensorIso_inv_pointed {E B : SSet.{u + 1}}
    (p : E ⟶ B) (K : SSet.{u + 1}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p) ≫
        (ihomCurryIso E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).inv := by
  apply (cancel_mono (ihomCurryIso E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← transportSquareTensorIso_hom_pointed, Iso.inv_hom_id_assoc]

/-- 概要：四角形の uncurrying の底側は元の内部 uncurrying。
方針：順方向の射影公式から二つの同型を消去する。
規約：底の分類図式を厳密に保つ。
使われ方：積上への表現の族の構成。 -/
lemma transportSquareTensorIso_inv_diagram {E B : SSet.{u + 1}}
    (p : E ⟶ B) (K : SSet.{u + 1}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso p K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K) =
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p) ≫
        (ihomCurryIso B K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).inv := by
  apply (cancel_mono (ihomCurryIso B K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← transportSquareTensorIso_hom_diagram, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
