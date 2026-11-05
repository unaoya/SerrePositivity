module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedPiCohomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedHomologyNaturality
/-!
概要：実 pinched 単体的加群の全基点 π と元の Hom コホモロジーの自然な比較。
方針：全基点 Moore チャートへ既存の Hom ホモロジー同型を合成する。
規約：全次数の鎖写像を使い、零基点へ制限しない。
使われ方：同じ coherent bar の評価コホモロジー余錐に渡す線形チャート。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison AlgebraicTopology HomologicalComplex
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

/-- 実線形化の任意の基点における、元の Hom コホモロジーへの群同型。 -/
def dgBarCompactPinchedModulePiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet (pinchedHomModule (S := R) x y)) n z ≃*
      Multiplicative ((homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactModulePiHomologyEquiv (pinchedHomModule (S := R) x y) n z).trans
    ((additiveGroupToMultiplicativeEquiv
      (pinchedHomMooreHomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv).trans
        (additiveGroupToMultiplicativeEquiv (ULift.moduleEquiv (R := R)).toAddEquiv))

lemma dgBarCompactPinchedModulePiCohomologyEquiv_naturality_of_truncation
    (φ : homObject R D x y ⟶ homObject R E a b)
    (ht : extendMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0))
      (ComplexShape.embeddingUpIntLE 0) ≫
        ((homObject R E a b).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv =
      ((homObject R D x y).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫
        truncLEMap φ (ComplexShape.embeddingUpIntLE 0))
    (n : ℕ) (z : (pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌))
    (α : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet (pinchedHomModule (S := R) x y)) n z) :
    dgBarCompactPinchedModulePiCohomologyEquiv a b n
        ((dgBarCompactPinchedModuleMap φ).app _ z)
        (dgBarCompactPiMap n (moduleUnderlyingSSetMap (dgBarCompactPinchedModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactPinchedModulePiCohomologyEquiv x y n z α) := by
  have h := ConcreteCategory.congr_hom
    (dgBarCompactPinchedHomMooreHomologyIso_naturality_of_truncation φ ht (n + 1))
      (dgBarCompactModulePiHomologyEquiv (pinchedHomModule (S := R) x y) n z α)
  dsimp only [dgBarCompactPinchedModulePiCohomologyEquiv, MulEquiv.trans_apply]
  rw [dgBarCompactModulePiHomologyEquiv_naturality]
  exact congrArg ULift.down h

end SerrePositivity.InfinityCategories
