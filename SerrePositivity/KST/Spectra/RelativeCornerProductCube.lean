module

public import SerrePositivity.KST.Spectra.RelativeCornerProductSource

/-!
概要：立方体の product 側の表示を、相対 latching とパラメーターの pushout-product と同定する。
方針：中央の二面の tensor 同型から外側の pushout 同型を作り、二包含で比較射を照合する。
規約：終域は恒等同型で固定する。
使われ方：Goerss–Jardine VII §4。相対 corner の Reedy anodyne 性への移送。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.WeightCornerPushout
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G)
  {A B : SSet.{u}} (i : A ⟶ B) (j : SimplexCategory)

/-- 相対 latching 射とパラメーターの射の実際の pushout-product。 -/
abbrev relativeProductSquare := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
  (relativeLatchingMap simplex j θ) i

/-- 立方体の外側の source から pushout-product の source への標準比較。 -/
abbrev productCubeSourceMap :=
  pushout.map
    (PushoutCube.middleLeft (RelativeWeightCornerCube.faceA (A := A) θ j))
    (PushoutCube.middleRight (RelativeWeightCornerCube.faceF (F := F) i j)
      (RelativeWeightCornerCube.faceTop θ i j))
    (relativeLatchingMap simplex j θ ▷ A) (relativeSource θ j ◁ i)
    (𝟙 (G.obj j ⊗ A)) (sourceTensorIso θ j B).hom (sourceTensorIso θ j A).hom
    ((Category.comp_id _).trans (sourceTensorIso_comparison θ j A).symm)
    (sourceTensorIso_natural θ i j)

instance productCubeSourceMap_isIso : IsIso (productCubeSourceMap θ i j) :=
  pushout.map_isIso _ _ _ _ (𝟙 _) (sourceTensorIso θ j B).hom (sourceTensorIso θ j A).hom _ _

/-- product 側の立方体表示は相対 latching 射の実際の pushout-product と同型。 -/
def productCubeArrowIso : Arrow.mk (RelativeWeightCornerCube.productFirst θ i j) ≅
    Arrow.mk (relativeProductSquare θ i j).ι := by
  refine Arrow.isoMk (asIso (productCubeSourceMap θ i j)) (Iso.refl _) ?_
  change productCubeSourceMap θ i j ≫ (relativeProductSquare θ i j).ι = _ ≫ 𝟙 _
  rw [Category.comp_id]
  dsimp only [RelativeWeightCornerCube.productFirst, PushoutCube.leftDesc]
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc]
    change (relativeProductSquare θ i j).inl ≫ (relativeProductSquare θ i j).ι = _
    rw [Functor.PushoutObjObj.inl_ι]
    exact (pushout.inl_desc _ _ _).symm
  · rw [← Category.assoc, pushout.inr_desc, Category.assoc]
    change (sourceTensorIso θ j B).hom ≫
      (relativeProductSquare θ i j).inr ≫ (relativeProductSquare θ i j).ι = _
    rw [Functor.PushoutObjObj.inr_ι]
    change (sourceTensorIso θ j B).hom ≫ (relativeLatchingMap simplex j θ ▷ B) = _
    rw [sourceTensorIso_comparison]
    exact (pushout.inr_desc _ _ _).symm

/-- corner の相対 latching は、重みの相対 latching とパラメーターの pushout-product。 -/
def relativeLatchingProductArrowIso :
    Arrow.mk (relativeLatchingMap simplex j (corner θ i).ι) ≅
      Arrow.mk (relativeProductSquare θ i j).ι :=
  relativeLatchingCubeArrowIso θ i j ≪≫ RelativeWeightCornerCube.arrowIso θ i j ≪≫
    productCubeArrowIso θ i j

/-- Reedy anodyne な重みの射と単射パラメーターの corner は Reedy anodyne。 -/
lemma corner_reedy_anodyne (hθ : reedyLeft simplex anodyneExtensions θ) [Mono i] :
    reedyLeft simplex anodyneExtensions (corner θ i).ι := by
  intro j
  exact (anodyneExtensions.arrow_iso_iff (relativeLatchingProductArrowIso θ i j)).mpr
    (anodyneExtensions_pushoutObjObjι' (relativeProductSquare θ i j) (hθ j))

end
end SerrePositivity.KST.Spectra.WeightCornerPushout
