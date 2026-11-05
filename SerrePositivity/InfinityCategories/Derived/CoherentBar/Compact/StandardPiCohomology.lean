module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.StandardMooreNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedCohomologyNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology DifferentialGraded DoldKanComparison HomologicalComplex
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

local instance (x y : D) : SSet.KanComplex
    (moduleUnderlyingSSet (standardModule (R := R) x y)) := standardHomSpaceKan x y
local instance (a b : E) : SSet.KanComplex
    (moduleUnderlyingSSet (standardModule (R := R) a b)) := standardHomSpaceKan a b

/-- 同じ標準加群の Moore ホモロジーと元の Hom コホモロジー。 -/
def dgBarCompactStandardMooreCohomologyIso (x y : D) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{u} R)).obj (standardModule (R := R) x y)).homology n ≅
      (homObject R D x y).homology (-(n : ℤ)) :=
  (homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso
      (standardNormalizationIso x y) ≪≫ connectiveHomHomologyIso x y n

lemma dgBarCompactStandardMooreCohomologyIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ) :
    homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
      (dgBarCompactStandardModuleMap φ)) n ≫
        (dgBarCompactStandardMooreCohomologyIso a b n).hom =
      (dgBarCompactStandardMooreCohomologyIso x y n).hom ≫
        homologyMap φ (-(n : ℤ)) := by
  have h := congrArg
    ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n).map)
    (dgBarCompactStandardNormalizationIso_naturality φ)
  simp only [Functor.map_comp] at h
  change homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
    (dgBarCompactStandardModuleMap φ)) n ≫ homologyMap (standardNormalizationIso a b).hom n =
      homologyMap (standardNormalizationIso x y).hom n ≫
        homologyMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n at h
  dsimp only [dgBarCompactStandardMooreCohomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  change (homologyMap ((normalizedMooreComplex (ModuleCat.{u} R)).map
    (dgBarCompactStandardModuleMap φ)) n ≫ homologyMap (standardNormalizationIso a b).hom n) ≫
      (connectiveHomHomologyIso a b n).hom =
    (homologyMap (standardNormalizationIso x y).hom n ≫
      (connectiveHomHomologyIso x y n).hom) ≫ homologyMap φ (-(n : ℤ))
  rw [h, Category.assoc, dgBarCompactConnectiveHomHomologyIso_naturality, Category.assoc]

/-- 元の全基点を保持する正次数チャート。 -/
def dgBarCompactStandardPiCohomologyEquiv (x y : D) (n : ℕ)
    (z : (standardModule (R := R) x y).obj (Opposite.op ⦋0⦌)) :
    KanHomotopyGroup (moduleUnderlyingSSet (standardModule (R := R) x y)) n z ≃*
      Multiplicative ((homObject R D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (dgBarCompactModulePiHomologyEquiv (standardModule (R := R) x y) n z).trans
    (additiveGroupToMultiplicativeEquiv
      (dgBarCompactStandardMooreCohomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv)

lemma dgBarCompactStandardPiCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ)
    (z : (standardModule (R := R) x y).obj (Opposite.op ⦋0⦌))
    (α : KanHomotopyGroup (moduleUnderlyingSSet (standardModule (R := R) x y)) n z) :
    dgBarCompactStandardPiCohomologyEquiv a b n
        ((dgBarCompactStandardModuleMap φ).app _ z)
        (dgBarCompactPiMap n (moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ)) z α) =
      homologyMap φ (-((n + 1 : ℕ) : ℤ))
        (dgBarCompactStandardPiCohomologyEquiv x y n z α) := by
  have h := ConcreteCategory.congr_hom
    (dgBarCompactStandardMooreCohomologyIso_naturality φ (n + 1))
      (dgBarCompactModulePiHomologyEquiv (standardModule (R := R) x y) n z α)
  dsimp only [dgBarCompactStandardPiCohomologyEquiv, MulEquiv.trans_apply]
  rw [dgBarCompactModulePiHomologyEquiv_naturality]
  exact h

/-- 零次数でも同じ正規化比較を使う。 -/
def dgBarCompactStandardPiZeroCohomologyEquiv (x y : D) :
    SSet.π₀ (moduleUnderlyingSSet (standardModule (R := R) x y)) ≃
      (homObject R D x y).homology 0 :=
  (modulePiZeroMooreEquiv (standardModule (R := R) x y)).trans
    (dgBarCompactStandardMooreCohomologyIso x y 0).toLinearEquiv.toEquiv

lemma dgBarCompactStandardPiZeroCohomologyEquiv_naturality
    (φ : homObject R D x y ⟶ homObject R E a b)
    (z : SSet.π₀ (moduleUnderlyingSSet (standardModule (R := R) x y))) :
    dgBarCompactStandardPiZeroCohomologyEquiv a b
        (SSet.mapπ₀ (moduleUnderlyingSSetMap (dgBarCompactStandardModuleMap φ)) z) =
      homologyMap φ 0 (dgBarCompactStandardPiZeroCohomologyEquiv x y z) := by
  have h := ConcreteCategory.congr_hom
    (dgBarCompactStandardMooreCohomologyIso_naturality φ 0)
      (modulePiZeroMooreEquiv (standardModule (R := R) x y) z)
  dsimp only [dgBarCompactStandardPiZeroCohomologyEquiv, Equiv.trans_apply]
  rw [modulePiZeroMooreEquiv_naturality]
  exact h

end SerrePositivity.InfinityCategories
