module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingBoundary
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathInversion
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

/-!
概要：cell 源の実乗法的写像模型は、標的の全擬同型を弱ホモトピー同値へ送る。
方針：全射の場合の全境界充填を反転し、元の実 mapping-path で一般の場合へ戻す。
規約：任意可換環と元の射。SSet や代数のモデル構造を仮定しない。
使われ方：元の擬同型 ∞ 局所化への導来写像空間比較の実標的不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) {X B : Mon (Complex R)} (q : X ⟶ B)

lemma multiplicativeCellMapping_anodyneImage_isIso (hq : QuasiIso q.hom) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (multiplicativeMappingPostcompose R (cellResolution R A) q)) := by
  apply map_isIso_of_inverts_surjective_quasiIso R
    (multiplicativeMappingFunctor R (cellResolution R A) ⋙ AnodyneHomotopy.anodyneQ)
    (fun p hs hp => MonoRightLiftingContraction.localized_isIso _
      (multiplicativeCellMapping_mono_rlp R A p hs hp)) q hq

lemma multiplicativeCellMapping_target_weakEquivalence (hq : QuasiIso q.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (multiplicativeMappingPostcompose R (cellResolution R A) q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (multiplicativeCellMapping_anodyneImage_isIso R A q hq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
