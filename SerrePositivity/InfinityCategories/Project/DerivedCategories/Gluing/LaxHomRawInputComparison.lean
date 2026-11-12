module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomRawInputActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedPairProjections
/-!
概要：正本比較の第二射影を元の左右 Hom 鎖射影の対へ厳密に同定する。
方針：元の入力射影を二成分へ分離し、一般宇宙の実 dg 関手作用を適用する。
規約：同じ全 Hom 入力と左右の順序を保持する。
使われ方：正本標的の区間座標と既存の入力付き四座標比較を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
lemma dgGluingLaxHomPullbackComparison_raw_inputs :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫ pullback.snd _ _ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomRawInputIso R C D M X Y).hom =
    lift
      ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)))
      ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u,max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomRawInputIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison_inputs_transport R C D M X Y]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tensorIso_hom, Category.assoc, tensorHom_fst, lift_fst,
      Iso.trans_hom]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPairMap_first]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLeftRawInput_action R C D M X Y
  · simp only [tensorIso_hom, Category.assoc, tensorHom_snd, lift_snd,
      Iso.trans_hom]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedPairMap_second]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomRightRawInput_action R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
