module
public import SerrePositivity.KST.SConstruction.PointedPushoutAnodyne
public import SerrePositivity.Spectra.Pointed.SmashPushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # 同じ元の smash pushout-product の anodyne 性
概要：一方が anodyne、他方が基礎単射なら、同じ smash pushout-product は anodyne。
方針：実際の直積境界を単体集合の pushout-product と照合し、smash への押し出しへ移す。
規約：ModelCategory の仮定を使わない。使われ方：円柱の端点と同じ実写像円柱の弱比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open PointedObject
variable {A B X Y : PointedSimplicialSet.{u}} (f : A ⟶ B) (g : X ⟶ Y)

/-- 同じ点つき実直積境界の忘却は、同じ基礎二射の実 pushout-product。 -/
def pointedUnderlyingProductSquare : (curriedTensor SSet.{u}).PushoutObjObj f.right g.right where
  pt := (productBoundary f g).right
  inl := (productBoundaryInl f g).right
  inr := (productBoundaryInr f g).right
  isPushout := by
    have h := (Under.forget (𝟙_ SSet.{u})).map_isPushout (productBoundary_isPushout f g)
    change IsPushout (f.right ▷ X.right) (A.right ◁ g.right)
      (productBoundaryInl f g).right (productBoundaryInr f g).right
    change IsPushout (prodMap f (𝟙 X)).right (prodMap (𝟙 A) g).right
      (productBoundaryInl f g).right (productBoundaryInr f g).right at h
    simp only [prodMap_right, Under.id_right, tensorHom_id, id_tensorHom] at h
    exact h
  ι := (productPushoutProduct f g).right
  inl_ι := by
    change (productBoundaryInl f g ≫ productPushoutProduct f g).right = B.right ◁ g.right
    simp only [productBoundaryInl_productPushoutProduct, prodMap_right,
      Under.id_right, id_tensorHom]
    rfl
  inr_ι := by
    change (productBoundaryInr f g ≫ productPushoutProduct f g).right = f.right ▷ Y.right
    simp only [productBoundaryInr_productPushoutProduct, prodMap_right,
      Under.id_right, tensorHom_id]
    rfl

/-- 同じ元の直積 pushout-product は、具体的 anodyne 類に入る。 -/
lemma pointedProductPushoutProduct_anodyne [Mono g.right] (hf : anodyneExtensions f.right) :
    anodyneExtensions (productPushoutProduct f g).right :=
  anodyneExtensions_pushoutObjObjι' (pointedUnderlyingProductSquare f g) hf

/-- 同じ元の smash pushout-product は、具体的 anodyne 類に入る。 -/
lemma pointedSmashPushoutProduct_anodyne [Mono g.right] (hf : anodyneExtensions f.right) :
    anodyneExtensions (smashPushoutProduct f g).right :=
  pointedIsPushout_anodyne_right (smashPushoutProduct_isPushout f g).flip
    (pointedProductPushoutProduct_anodyne f g hf)

end SerrePositivity.KST.SConstruction
