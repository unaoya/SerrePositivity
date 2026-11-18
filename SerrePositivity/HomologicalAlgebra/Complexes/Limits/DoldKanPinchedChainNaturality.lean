module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanGammaChainNaturality

/-!
# 実 Γ Hom と dg nerve の同じ Hom 鎖写像への自然性

概要：元の実 DK/pinched 同型は任意の Hom 鎖写像の Γ 像と可換である。
方針：元の小さい線形模型・実 Γ 同型・同じ宇宙持ち上げの全自然性を合成する。
規約：元の doldKanHomPinchedIso と pinchedHomChainMap を保つ。
使われ方：正規化 Hom の前後作用と ∞ 写像空間の作用の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

def doldKanHomSpaceChainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x' y' :=
  Functor.whiskerRight
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
      (truncLE'Map f (ComplexShape.embeddingUpIntLE 0))) (forget (ModuleCat R))

lemma homSpaceDoldKanIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.homModuleChainMap f) (forget (ModuleCat R)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x' y').hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x y).hom ≫ _root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap f := by
  change Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.homModuleChainMap f) (forget (ModuleCat R)) ≫
      Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso (R := R) x' y').hom (forget (ModuleCat R)) =
    Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso (R := R) x y).hom (forget (ModuleCat R)) ≫
      Functor.whiskerRight _ (forget (ModuleCat R))
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, _root_.SerrePositivity.ComplexLimits.homModuleDoldKanIso_chainMap]

lemma homSpaceDoldKanIso_inv_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    _root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x' y').inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x y).inv ≫
        Functor.whiskerRight (_root_.SerrePositivity.ComplexLimits.homModuleChainMap f) (forget (ModuleCat R)) := by
  apply (Iso.eq_inv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x y)).mpr
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homSpaceDoldKanIso (R := R) x' y')).mpr
  exact (_root_.SerrePositivity.ComplexLimits.homSpaceDoldKanIso_chainMap f).symm

lemma doldKanHomPinchedIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    SSet.uliftFunctor.{v, u}.map (_root_.SerrePositivity.ComplexLimits.doldKanHomSpaceChainMap f) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := R) x' y').hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso (R := R) x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap f := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, _root_.SerrePositivity.ComplexLimits.homSpaceDoldKanIso_inv_chainMap,
    SSet.uliftFunctor.map_comp, Category.assoc, _root_.SerrePositivity.ComplexLimits.homSpaceLiftIso_chainMap]
  simp only [Category.assoc]

end SerrePositivity.ComplexLimits
