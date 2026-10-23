module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantPullbackCoordinates

/-!
概要：定値 unstraightening への相対射の族の評価を、fiber と元の底の二座標へ分解する。
方針：fiber の包含と底の射影で二成分を照合する。
規約：元の相対射の全パラメータを厳密に保持する。
使われ方：相対合成を fiber 上の元の写像の評価として計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の相対評価の直積座標は fiber 内部 Hom の評価と元の底への射影。
方針：二座標で同定し、fiber 側は包含後の比較で判定する。
規約：全パラメータの等式。使われ方：定値標的への相対写像の再構成。 -/
lemma constantUnstraighteningRelativeIso_coordinates {A B T : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (k : T ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) a) :
    relativeFunctorUncurry k ≫ (constantPullbackFiberIso pointedSpaceProjection z).hom =
      lift (uncurry (k ≫ (constantUnstraighteningRelativeIso a z).hom)) (fst A T ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    apply vertexFiber_hom_ext
    rw [Category.assoc, Category.assoc, constantPullbackFiberIso_fst_ι,
      constantUnstraighteningRelativeIso_uncurry]
  · rw [Category.assoc, constantPullbackFiberIso_snd, lift_snd]
    exact relativeFunctorUncurry_projection k

/-- 概要：元の相対評価を fiber の評価と底への射影から厳密に回収する。
方針：二座標の表示に直積比較の逆を続ける。
規約：元の評価そのもの。使われ方：fiber の座標を用いた相対合成の評価。 -/
lemma constantUnstraighteningRelativeIso_reconstruct {A B T : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (k : T ⟶ relativeFunctorSpace
      (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) a) :
    relativeFunctorUncurry k =
      lift (uncurry (k ≫ (constantUnstraighteningRelativeIso a z).hom)) (fst A T ≫ a) ≫
        (constantPullbackFiberIso pointedSpaceProjection z).inv := by
  have h := congrArg (fun q ↦ q ≫ (constantPullbackFiberIso pointedSpaceProjection z).inv)
    (constantUnstraighteningRelativeIso_coordinates a z k)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

end SerrePositivity.InfinityCategories.F2
