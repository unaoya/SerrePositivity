module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedModuleCohomology
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology DifferentialGraded DoldKanComparison HomologicalComplex
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

lemma dgBarCompactConnectiveHomHomologyIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ) :
    homologyMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n ≫
      (connectiveHomHomologyIso a b n).hom =
    (connectiveHomHomologyIso x y n).hom ≫ homologyMap φ (-(n : ℤ)) :=
  dgBarCompactConnectiveHomHomologyIso_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n

lemma dgBarCompactPinchedHomMooreHomologyIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ) :
    homologyMap ((normalizedMooreComplex (ModuleCat.{max u v} R)).map
      (dgBarCompactPinchedModuleMap φ)) n ≫ (pinchedHomMooreHomologyIso a b n).hom =
      (pinchedHomMooreHomologyIso x y n).hom ≫
        (ModuleCat.uliftFunctor.{v} R).map (homologyMap φ (-(n : ℤ))) :=
  dgBarCompactPinchedHomMooreHomologyIso_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n

lemma dgBarCompactPinchedModulePiCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b)
    (n : ℕ) (z : (pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌))
    (α : KanHomotopyGroup (moduleUnderlyingSSet (pinchedHomModule (S := R) x y)) n z) :
    dgBarCompactPinchedModulePiCohomologyEquiv a b n
        ((dgBarCompactPinchedModuleMap φ).app _ z)
        (dgBarCompactPiMap n (moduleUnderlyingSSetMap (dgBarCompactPinchedModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactPinchedModulePiCohomologyEquiv x y n z α) :=
  dgBarCompactPinchedModulePiCohomologyEquiv_naturality_of_truncation φ
    (SerrePositivity.EInfinity.ComplexLimits.truncLEIso_inv_naturality φ
      (ComplexShape.embeddingUpIntLE 0)) n z α

end SerrePositivity.InfinityCategories
