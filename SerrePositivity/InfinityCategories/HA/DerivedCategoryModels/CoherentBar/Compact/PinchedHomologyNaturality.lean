module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedMooreNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.TruncationHomologyNaturality
/-!
概要：実 pinched Moore ホモロジーの比較に、元の全 Hom 鎖写像の自然性を与える。
方針：複体同型の自然性、正確な宇宙交換、非正切断のホモロジー自然性を合成する。
規約：E2 所有の切断自然性は明示された等式として受け取り、本文をコピーしない。
使われ方：全基点の π チャートの脚自然性を、元の評価コホモロジーへ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded HomologicalComplex
variable {R : Type u} [CommRing R]

lemma dgBarCompactUliftHomologyIso_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (n : ℕ) :
    homologyMap (((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (.down ℕ)).map φ) n ≫
      ((L.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{v} R)).hom =
    ((K.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{v} R)).hom ≫
      (ModuleCat.uliftFunctor.{v} R).map (homologyMap φ n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.down ℕ) n).map φ)
    (ModuleCat.uliftFunctor.{v} R)

variable {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E] {x y : D} {a b : E}

lemma dgBarCompactPinchedHomMooreHomologyIso_naturality_of_truncation
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b)
    (ht : extendMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0))
      (ComplexShape.embeddingUpIntLE 0) ≫
        ((_root_.SerrePositivity.DifferentialGraded.homObject R E a b).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv =
      ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫
        truncLEMap φ (ComplexShape.embeddingUpIntLE 0)) (n : ℕ) :
    homologyMap ((normalizedMooreComplex (ModuleCat.{max u v} R)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ)) n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso a b n).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y n).hom ≫
        (ModuleCat.uliftFunctor.{v} R).map (homologyMap φ (-(n : ℤ))) := by
  have h₁ := congrArg (fun f => homologyMap f n)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedHomMooreIso_naturality φ)
  simp only [homologyMap_comp] at h₁
  have h₂ := dgBarCompactUliftHomologyIso_naturality.{u, v}
    (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n
  have h₃ := congrArg ((ModuleCat.uliftFunctor.{v} R).map)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactConnectiveHomHomologyIso_naturality_of_truncation φ ht n)
  simp only [Functor.map_comp] at h₃
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, HomologicalComplex.homologyFunctor_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex]
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc _ _
    ((ModuleCat.uliftFunctor.{v} R).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso a b n).hom), h₂]
  simp only [Category.assoc]
  rw [h₃]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
