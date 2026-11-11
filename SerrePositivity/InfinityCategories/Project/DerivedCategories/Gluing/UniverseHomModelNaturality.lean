module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseHomChainMapComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommonComplexUniverseIso

/-! 一般宇宙の実 Hom 鎖写像は、単位 Hom 模型と対象宇宙変更を厳密に保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : C} {x' y' : D}

lemma dgGluingUniverseComplexPinchedMap_eq {K L : _root_.SerrePositivity.DifferentialGraded.Complex R} (φ : K ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, max u v w r}
      (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} K) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, w} L)
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
      (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
      (_root_.SerrePositivity.DifferentialGraded.homPostcompose (𝟙_ (_root_.SerrePositivity.DifferentialGraded.Complex R)) φ) =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} L).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, w} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, w} L) n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s.down)).toPinched) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, v, w} L n.unop.len
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex (homPostcompose (𝟙_ (Complex R)) φ) s.down))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  rfl

lemma dgGluingUniverseHomModel_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, max u v w r} φ ≫
      (SSet.uliftFunctor.{max u v w r, max u w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').hom =
    (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom ≫
      (SSet.uliftFunctor.{max u v w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, v, w, r} (homObject R D x' y')).hom := by
  have hpost := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_post.{u, v, w, max u v w r}
    (C := C) (D := D) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, w} (homObject R D x' y'))
    (x'' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y'' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
    φ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homObject R D x' y')).hom
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap φ ≫
    (SSet.uliftFunctor.{max u v w r, max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').hom = _
    at hpost
  rw [hpost]
  have hpre := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_pre.{u, v, w, max u v w r}
    (C := C) (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, v} (homObject R C x y))
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, w} (homObject R D x' y'))
    (a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso (homObject R C x y)).hom (homPostcompose (𝟙_ (Complex R)) φ)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality φ, ← hpre]
  change (SSet.uliftFunctor.{max u v w r, max u v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom ≫ _ = _
  rw [dgGluingUniverseComplexPinchedMap_eq.{u, v, w, r}]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
