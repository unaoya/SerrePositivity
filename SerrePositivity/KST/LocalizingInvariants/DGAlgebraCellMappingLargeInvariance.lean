module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeKan
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingTargetInvariance
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition

/-!
概要：大宇宙の実 cell 写像関手は、元の標的擬同型を同じ写像の空間同値へ送る。
方針：既に証明した弱ホモトピー同値を Kan 間の同値とし、元の宇宙持ち上げに適用する。
規約：実 Kan 写像自身について述べ、代数や単体集合のモデル構造を入力しない。
使われ方：指定された擬同型 ∞ 局所化に対する実写像模型の不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

lemma multiplicativeCellMappingLarge_target_isQCatEquivalence {X Y : Mon (Complex R)}
    (q : X ⟶ Y) (hq : QuasiIso q.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((multiplicativeCellMappingLargeKanFunctor R A).obj X).obj ⟶
        ((multiplicativeCellMappingLargeKanFunctor R A).obj Y).obj from
          (multiplicativeCellMappingLargeKanFunctor R A).map q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
      (multiplicativeCellMapping_target_weakEquivalence R A q hq).isSimplicialHomotopyEquivalence)

set_option maxHeartbeats 800000 in -- 元の ULiftHom 射と cell 写像関手の実写像を照合する。
lemma multiplicativeCellMappingInfinity_target_isQCatEquivalence
    {X Y : InfinityPresentation R} (q : X ⟶ Y) (hq : QuasiIso q.down.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (show ((multiplicativeCellMappingInfinityKanFunctor R A).obj X).obj ⟶
        ((multiplicativeCellMappingInfinityKanFunctor R A).obj Y).obj from
          (multiplicativeCellMappingInfinityKanFunctor R A).map q) :=
  multiplicativeCellMappingLarge_target_isQCatEquivalence R A q.down hq

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
