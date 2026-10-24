module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPairProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry
/-!
概要：入力座標の逆同型の全 join 族を、元の二つの入力の全 join 族へ分離する。
方針：端点輸送は元の図式を変えず、積の pinched Hom の逆は各値を対にすることを用いる。
規約：空の入力にも固定終点を保持する。
使われ方：正本標的の底の二作用を元 Hom 複体上で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
lemma dgGluingPinchedEndpointIso_inv_uncurry {T X : SSet.{u}}
    {x y x' y' : X _⦋0⦌} (hx : x = x') (hy : y = y') (a : T ⟶ pinchedHom x' y') :
    pinchedHomUncurry (a ≫ (pinchedEndpointIso hx hy).inv) = pinchedHomUncurry a := by
  subst x'
  subst y'
  simp only [pinchedEndpointIso, Iso.refl_inv, Category.comp_id]
lemma dgGluingPinchedTensorIso_inv_first {X Y : SSet.{u}} (x y : (X ⊗ Y) _⦋0⦌) :
    (F2.pinchedHomTensorIso x y).inv ≫ pinchedHomMap (fst X Y) x y = fst _ _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply PinchedHom.Simplex.ext
  rfl
lemma dgGluingPinchedTensorIso_inv_second {X Y : SSet.{u}} (x y : (X ⊗ Y) _⦋0⦌) :
    (F2.pinchedHomTensorIso x y).inv ≫ pinchedHomMap (snd X Y) x y = snd _ _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply PinchedHom.Simplex.ext
  rfl
lemma dgGluingPinchedTensorIso_inv_first_uncurry {T X Y : SSet.{u}}
    (x y : (X ⊗ Y) _⦋0⦌) (h : T ⟶ pinchedHom x.1 y.1 ⊗ pinchedHom x.2 y.2) :
    pinchedHomUncurry (h ≫ (F2.pinchedHomTensorIso x y).inv) ≫ fst X Y =
      pinchedHomUncurry (h ≫ fst _ _) := by
  rw [← pinchedHomUncurry_postcomp, Category.assoc, dgGluingPinchedTensorIso_inv_first]
lemma dgGluingPinchedTensorIso_inv_second_uncurry {T X Y : SSet.{u}}
    (x y : (X ⊗ Y) _⦋0⦌) (h : T ⟶ pinchedHom x.1 y.1 ⊗ pinchedHom x.2 y.2) :
    pinchedHomUncurry (h ≫ (F2.pinchedHomTensorIso x y).inv) ≫ snd X Y =
      pinchedHomUncurry (h ≫ snd _ _) := by
  rw [← pinchedHomUncurry_postcomp, Category.assoc, dgGluingPinchedTensorIso_inv_second]
end SerrePositivity.InfinityCategories
