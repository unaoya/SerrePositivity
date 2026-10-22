module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomChainMapComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseIso

/-! 一般宇宙の実 Hom 鎖写像は、単位 Hom 模型と対象宇宙変更を厳密に保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] {x y : C} {x' y' : D}

lemma dgGluingUniverseComplexPinchedMap_eq {K L : Complex R} (φ : K ⟶ L) :
    dgGluingUniverseHomChainMap.{u, v, w, max u v w r}
      (C := DGComplexPinchedModel.{u, v} K) (D := DGComplexPinchedModel.{u, w} L)
      (x := complexPinchedSource K) (y := complexPinchedTarget K)
      (x' := complexPinchedSource L) (y' := complexPinchedTarget L)
      (homPostcompose (𝟙_ (Complex R)) φ) =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} L).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv (complexPinchedSource.{u, w} L)
    (complexPinchedTarget.{u, w} L) n.unop.len).injective
  change toLinearSimplex ((pinchedLinearSimplexMap _ (toLinearSimplex s.down)).toPinched) =
    toLinearSimplex (dgGluingComplexPinchedUniverseEquiv.{u, v, w} L n.unop.len
      (pinchedHomChainMapSimplex (homPostcompose (𝟙_ (Complex R)) φ) s.down))
  rw [LinearSimplex.toLinearSimplex_toPinched, dgGluingComplexPinchedUniverseEquiv_linear,
    pinchedHomChainMapSimplex_linear]
  rfl

lemma dgGluingUniverseHomModel_naturality
    (φ : homObject R C x y ⟶ homObject R D x' y') :
    dgGluingUniverseHomChainMap.{u, v, w, max u v w r} φ ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map
        (pinchedComplexModelIso x' y').hom =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (pinchedComplexModelIso x y).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u v}).map (complexPinchedMap.{u, v} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} (homObject R D x' y')).hom := by
  have hpost := dgGluingUniverseHomChainMap_post.{u, v, w, max u v w r}
    (C := C) (D := D) (E := DGComplexPinchedModel.{u, w} (homObject R D x' y'))
    (x'' := complexPinchedSource _) (y'' := complexPinchedTarget _)
    φ (complexUnitHomIso (homObject R D x' y')).hom
  change dgGluingUniverseHomChainMap φ ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map (pinchedComplexModelIso x' y').hom = _
    at hpost
  rw [hpost]
  have hpre := dgGluingUniverseHomChainMap_pre.{u, v, w, max u v w r}
    (C := C) (T := DGComplexPinchedModel.{u, v} (homObject R C x y))
    (D := DGComplexPinchedModel.{u, w} (homObject R D x' y'))
    (a := complexPinchedSource _) (b := complexPinchedTarget _)
    (x' := complexPinchedSource _) (y' := complexPinchedTarget _)
    (complexUnitHomIso (homObject R C x y)).hom (homPostcompose (𝟙_ (Complex R)) φ)
  rw [← complexUnitHomIso_naturality φ, ← hpre]
  change (SSet.uliftFunctor.{max u v w r, max u v}).map
    (pinchedComplexModelIso x y).hom ≫ _ = _
  rw [dgGluingUniverseComplexPinchedMap_eq.{u, v, w, r}]

end SerrePositivity.InfinityCategories
