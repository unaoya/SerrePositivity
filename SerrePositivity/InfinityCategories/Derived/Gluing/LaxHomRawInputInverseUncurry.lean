module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomRawInputIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedInputCoordinateUncurry
/-!
概要：正本入力座標の逆の全 join 族を、元左右 Hom 模型同型の逆へ厳密に分離する。
方針：全体と各因子の端点輸送を除き、積の pinched Hom の逆の両射影を適用する。
規約：空のパラメーターにも固定終点を保ち、二つの全入力を変更しない。
使われ方：正本標的の底の二作用を元の二作用と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomRawInputIso_inv_first_uncurry :
    pinchedHomUncurry (dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      fst ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C))
        ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (dgNerve R D)) =
    pinchedHomUncurry (fst _ _ ≫ (dgGluingLaxHomLeftRawInputIso R C D M X Y).inv) := by
  dsimp only [dgGluingLaxHomRawInputIso, Iso.trans_inv,
    dgGluingLaxHomInputEndpointIso, dgGluingPinchedCompositeIso]
  rw [dgGluingPinchedEndpointIso_inv_uncurry,
    dgGluingPinchedTensorIso_inv_first_uncurry]
  simp only [tensorIso_inv, tensorHom_fst, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc, dgGluingPinchedEndpointIso_inv_uncurry]
lemma dgGluingLaxHomRawInputIso_inv_second_uncurry :
    pinchedHomUncurry (dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      snd ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C))
        ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (dgNerve R D)) =
    pinchedHomUncurry (snd _ _ ≫ (dgGluingLaxHomRightRawInputIso R C D M X Y).inv) := by
  dsimp only [dgGluingLaxHomRawInputIso, Iso.trans_inv,
    dgGluingLaxHomInputEndpointIso, dgGluingPinchedCompositeIso]
  rw [dgGluingPinchedEndpointIso_inv_uncurry,
    dgGluingPinchedTensorIso_inv_second_uncurry]
  simp only [tensorIso_inv, tensorHom_snd, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc, dgGluingPinchedEndpointIso_inv_uncurry]
end SerrePositivity.InfinityCategories
