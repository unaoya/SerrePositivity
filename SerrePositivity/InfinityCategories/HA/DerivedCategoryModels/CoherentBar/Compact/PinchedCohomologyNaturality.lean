module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedModuleCohomology
public import SerrePositivity.HomologicalAlgebra.ComplexLimits.TruncationInclusionNaturality
/-!
概要：全基点 pinched コホモロジーチャートの自然性から、切断比較の明示引数を解消する。
方針：E2 所有の dg 最小上流入口の切断自然性を、検証済みの比較へ代入する。
規約：上流の宣言・本文を保持し、EInfinity 固有の import は導入しない。
使われ方：実評価の transition と脚のコホモロジー比較に使う無条件入口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

lemma dgBarCompactConnectiveHomHomologyIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) (n : ℕ) :
    homologyMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso a b n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso x y n).hom ≫ homologyMap φ (-(n : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactConnectiveHomHomologyIso_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n

lemma dgBarCompactPinchedHomMooreHomologyIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) (n : ℕ) :
    homologyMap ((normalizedMooreComplex (ModuleCat.{max u v} R)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ)) n ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso a b n).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y n).hom ≫
        (ModuleCat.uliftFunctor.{v} R).map (homologyMap φ (-(n : ℤ))) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedHomMooreHomologyIso_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n

lemma dgBarCompactPinchedModulePiCohomologyEquiv_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b)
    (n : ℕ) (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌))
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y)) n z) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModulePiCohomologyEquiv a b n
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ).app _ z)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModulePiCohomologyEquiv x y n z α) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModulePiCohomologyEquiv_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n z α

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
