module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedPiCohomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedHomologyNaturality
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded AlgebraicTopology HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

/-- 実線形化の任意の基点における、元の Hom コホモロジーへの群同型。 -/
def dgBarCompactPinchedModulePiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y)) n z ≃*
      Multiplicative ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y) n z).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv).trans
        (_root_.SerrePositivity.InfinityCategories.HA.Section1_2_3.additiveGroupToMultiplicativeEquiv (ULift.moduleEquiv (R := R)).toAddEquiv))

lemma dgBarCompactPinchedModulePiCohomologyEquiv_naturality_of_truncation
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b)
    (ht : extendMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0))
      (ComplexShape.embeddingUpIntLE 0) ≫
        ((_root_.SerrePositivity.DifferentialGraded.homObject R E a b).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv =
      ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫
        truncLEMap φ (ComplexShape.embeddingUpIntLE 0))
    (n : ℕ) (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y).obj (Opposite.op ⦋0⦌))
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y)) n z) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModulePiCohomologyEquiv a b n
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ).app _ z)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactPinchedModulePiCohomologyEquiv x y n z α) := by
  have h := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPinchedHomMooreHomologyIso_naturality_of_truncation φ ht (n + 1))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := R) x y) n z α)
  dsimp only [dgBarCompactPinchedModulePiCohomologyEquiv, MulEquiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv_naturality]
  exact congrArg ULift.down h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
