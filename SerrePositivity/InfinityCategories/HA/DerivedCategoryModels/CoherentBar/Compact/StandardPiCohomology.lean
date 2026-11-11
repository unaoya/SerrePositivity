module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.StandardMooreNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedCohomologyNaturality
/-!
概要：標準単体的加群の全基点 π と元の Hom コホモロジーを自然に比較する。
方針：Moore 正規化・smart truncation の自然同型を全基点チャートへ合成する。
規約：実鎖写像と全基点を保持し、正次数は n+1 とする。
使われ方：反転・宇宙持ち上げの線形模型を native 評価余錐へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology DifferentialGraded HomologicalComplex
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

local instance (x y : D) : SSet.KanComplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan x y
local instance (a b : E) : SSet.KanComplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) a b)) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan a b

/-- 同じ標準加群の Moore ホモロジーと元の Hom コホモロジー。 -/
def dgBarCompactStandardMooreCohomologyIso (x y : D) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).homology n ≅
      (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology (-(n : ℤ)) :=
  (homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso x y) ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso x y n

lemma dgBarCompactStandardMooreCohomologyIso_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) (n : ℕ) :
    homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) n ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardMooreCohomologyIso a b n).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardMooreCohomologyIso x y n).hom ≫
        homologyMap φ (-(n : ℤ)) := by
  have h := congrArg
    ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardNormalizationIso_naturality φ)
  simp only [Functor.map_comp] at h
  change homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) n ≫ homologyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso a b).hom n =
      homologyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso x y).hom n ≫
        homologyMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n at h
  dsimp only [dgBarCompactStandardMooreCohomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  change (homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) n ≫ homologyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso a b).hom n) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso a b n).hom =
    (homologyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso x y).hom n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso x y n).hom) ≫ homologyMap φ (-(n : ℤ))
  rw [h, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactConnectiveHomHomologyIso_naturality, Category.assoc]

/-- 元の全基点を保持する正次数チャート。 -/
def dgBarCompactStandardPiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)) n z ≃*
      Multiplicative ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n z).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.additiveGroupToMultiplicativeEquiv
      (dgBarCompactStandardMooreCohomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv)

lemma dgBarCompactStandardPiCohomologyEquiv_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y).obj (Opposite.op ⦋0⦌))
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)) n z) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardPiCohomologyEquiv a b n
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ).app _ z)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactStandardPiCohomologyEquiv x y n z α) := by
  have h := ConcreteCategory.congr_hom
    (dgBarCompactStandardMooreCohomologyIso_naturality φ (n + 1))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n z α)
  dsimp only [dgBarCompactStandardPiCohomologyEquiv, MulEquiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv_naturality]
  exact h

/-- 零次数でも同じ正規化比較を使う。 -/
def dgBarCompactStandardPiZeroCohomologyEquiv (x y : D) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)) ≃
      (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).homology 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).trans
    (dgBarCompactStandardMooreCohomologyIso x y 0).toLinearEquiv.toEquiv

lemma dgBarCompactStandardPiZeroCohomologyEquiv_naturality
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b)
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y))) :
    dgBarCompactStandardPiZeroCohomologyEquiv a b
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap φ)) z) =
      homologyMap φ 0 (dgBarCompactStandardPiZeroCohomologyEquiv x y z) := by
  have h := ConcreteCategory.congr_hom
    (dgBarCompactStandardMooreCohomologyIso_naturality φ 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) z)
  dsimp only [dgBarCompactStandardPiZeroCohomologyEquiv, Equiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv_naturality]
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
