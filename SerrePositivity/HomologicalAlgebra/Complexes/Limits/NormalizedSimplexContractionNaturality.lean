module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainContraction

/-!
# 標準単体の実 augmentation の自然性

概要：正規化単体収縮の順方向の射は全ての面・退化に自然。
方針：Moore 包含と元の交代面 augmentation の自然性を合成する。
規約：逆の収縮の自然性は要求せず、同じ augmentation の射を保持する。
使われ方：正規化単体テンソルの全 augmentation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]

lemma normalizedSimplexChainContraction_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map
      ((linearization A).map (SSet.stdSimplex.map f)) ≫
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A m).hom =
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom := by
  let J := SSet.Augmented.stdSimplex ⋙
    (SimplicialObject.Augmented.whiskering _ _).obj (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)
  have h := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := ModuleCat A)).naturality
    (J.map f)
  have hi := (AlgebraicTopology.inclusionOfMooreComplex (ModuleCat A)).naturality
    ((linearization A).map (SSet.stdSimplex.map f))
  change _ ≫ AlgebraicTopology.inclusionOfMooreComplexMap _ =
    AlgebraicTopology.inclusionOfMooreComplexMap _ ≫ _ at hi
  let c := (ChainComplex.single₀ (ModuleCat A)).mapIso
    ((uliftFunctor.{u, 0} ⋙ ModuleCat.free A).mapIso Limits.Types.terminalIso ≪≫ singletonFreeIso A)
  change _ ≫ (AlgebraicTopology.inclusionOfMooreComplexMap _ ≫
    AlgebraicTopology.AlternatingFaceMapComplex.ε.app (J.obj m) ≫ c.hom) =
    AlgebraicTopology.inclusionOfMooreComplexMap _ ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app (J.obj n) ≫ c.hom
  erw [← Category.assoc, hi, Category.assoc, ← Category.assoc _ _ c.hom, h]
  have hr : (J.map f).right = 𝟙 _ := by
    change (uliftFunctor.{u, 0} ⋙ ModuleCat.free A).map
      (Limits.terminal.from (Limits.terminal (Type))) = 𝟙 _
    rw [show Limits.terminal.from (Limits.terminal (Type)) = 𝟙 _ from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  simp only [Functor.comp_map, SimplicialObject.Augmented.point_map, hr]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  erw [Category.id_comp]
  rfl

lemma normalizedSimplexCochainContraction_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (normalizedFunctor A).map (SSet.stdSimplex.map f) ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A m).hom =
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom := by
  change HomologicalComplex.extendMap _ ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendMap _ ComplexShape.embeddingDownNat ≫ _) = _
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction_naturality]
  rfl

end SerrePositivity.ComplexLimits
