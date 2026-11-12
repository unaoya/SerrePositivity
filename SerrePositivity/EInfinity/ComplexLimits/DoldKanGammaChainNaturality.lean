module

public import SerrePositivity.EInfinity.ComplexLimits.DoldKanNormalizationNaturality

/-!
# 元の実 Γ 同型の任意の Hom 鎖写像への自然性

概要：同じ線形模型から実 Γ への同型は元の Hom 鎖写像の smart 切断像と可換。
方針：Dold–Kan 同値の unit の自然性と元の正規化同型の自然性を合成する。
規約：元の同じ standardDoldKanModuleIso と homModuleDoldKanIso を使う。
使われ方：Γ の写像と dg nerve の pinched Hom 写像の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {x' y' : E}

lemma standardModuleIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x y).hom ≫ standardModuleChainMap f =
      homModuleChainMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModuleIso (R := R) x' y').hom := by
  simp only [standardModuleChainMap, Iso.hom_inv_id_assoc]

lemma standardDoldKanModuleIso_chainMap
    (f : homObject R D x y ⟶ homObject R E x' y') :
    standardModuleChainMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x' y').hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom ≫
        (Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
          (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) := by
  let G : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R) := Abelian.DoldKan.Γ
  have h := (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
    ChainComplex (ModuleCat R) ℕ).unitIso.hom.naturality (standardModuleChainMap f)
  change standardModuleChainMap f ≫
      (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
        ChainComplex (ModuleCat R) ℕ).unitIso.hom.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x' y') =
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).unitIso.hom.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) ≫
        G.map ((normalizedMooreComplex (ModuleCat R)).map (standardModuleChainMap f)) at h
  change standardModuleChainMap f ≫
      ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
        ChainComplex (ModuleCat R) ℕ).unitIso.hom.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x' y') ≫
        G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x' y').hom) =
    ((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).unitIso.hom.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) ≫
        G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom) ≫
          G.map (truncLE'Map f (ComplexShape.embeddingUpIntLE 0))
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp,
    standardNormalizationIso_chainMap, G.map_comp, Category.assoc]

lemma homModuleDoldKanIso_chainMap (f : homObject R D x y ⟶ homObject R E x' y') :
    homModuleChainMap f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso (R := R) x' y').hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso (R := R) x y).hom ≫
        (Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
          (truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.homModuleDoldKanIso, Iso.trans_hom]
  rw [← Category.assoc, ← standardModuleIso_chainMap, Category.assoc,
    standardDoldKanModuleIso_chainMap]
  simp only [Category.assoc]

end SerrePositivity.EInfinity.ComplexLimits
