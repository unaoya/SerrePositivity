module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedModuleMap
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardMooreNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.MooreUliftNaturality
/-!
概要：実 pinched 空間の Moore 比較と元の Hom 鎖写像との自然性を示す。
方針：座標・標準正規化・宇宙交換の三つの可換式を合成する。
規約：同じ既存の pinchedHomMooreIso を使い、対象宇宙を独立に保つ。
使われ方：native 評価の実脚への全次数ホモロジーチャートの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology DifferentialGraded DoldKanComparison
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

lemma dgBarCompactStandardModuleIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) :
    dgBarCompactLinearHomModuleMap φ ≫ (standardModuleIso a b).hom =
      (standardModuleIso x y).hom ≫ dgBarCompactStandardModuleMap φ := by
  ext n s
  change standardSimplexEquiv a b n.unop.len (pinchedLinearSimplexMap φ s) =
    standardSimplexEquiv a b n.unop.len (pinchedLinearSimplexMap φ
      ((standardSimplexEquiv x y n.unop.len).symm (standardSimplexEquiv x y n.unop.len s)))
  rw [LinearEquiv.symm_apply_apply]

lemma dgBarCompactHomModuleMooreIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) :
    (normalizedMooreComplex (ModuleCat.{u} R)).map (dgBarCompactLinearHomModuleMap φ) ≫
      (homModuleMooreIso a b).hom =
    (homModuleMooreIso x y).hom ≫
      HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0) := by
  simp only [homModuleMooreIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, dgBarCompactStandardModuleIso_naturality,
    Functor.map_comp, Category.assoc, dgBarCompactStandardNormalizationIso_naturality]
  simp only [Category.assoc]

/-- 全次数・実 pinched 射の Moore 正規化比較の自然性。 -/
lemma dgBarCompactPinchedHomMooreIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) :
    (normalizedMooreComplex (ModuleCat.{max u v} R)).map (dgBarCompactPinchedModuleMap φ) ≫
      (pinchedHomMooreIso a b).hom =
    (pinchedHomMooreIso x y).hom ≫
      ((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (.down ℕ)).map
        (HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) := by
  simp only [pinchedHomMooreIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    dgBarCompactPinchedModuleMap_coordinate, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ _
    (((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (.down ℕ)).map
      (homModuleMooreIso a b).hom), dgBarCompactMooreUliftIso_naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp, dgBarCompactHomModuleMooreIso_naturality, Functor.map_comp]

end SerrePositivity.InfinityCategories
