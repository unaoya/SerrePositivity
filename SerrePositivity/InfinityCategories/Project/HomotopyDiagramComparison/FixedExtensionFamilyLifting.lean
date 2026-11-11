module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedExtensionCurry

/-!
概要：底と初期値を固定する実際の族を、任意の単射なパラメータ境界から延長する。
方針：元の族を可縮な相対延長空間へ戻し、その全境界持ち上げを raw な族へ展開する。
規約：元の境界族・底・初期値を同時に厳密に保つ。パラメータの Kan 性は不要。
使われ方：輸送比較の円柱や高次の境界を一つの整合する族として埋める。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 固定した底と初期値を持つ全パラメータ族は、任意の単射な境界から延長できる。 -/
lemma exists_fixedExtensionFamily_of_mono {A D K L E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (β : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (k : K ⟶ L) [Mono k] (W : A ⊗ K ⟶ E)
    (hW : W ≫ p = fst A K ≫ β) (hI : (i ▷ K) ≫ W = fst D K ≫ v) :
    ∃ U : A ⊗ L ⟶ E,
      U ≫ p = fst A L ≫ β ∧
      (i ▷ L) ≫ U = fst D L ≫ v ∧ (A ◁ k) ≫ U = W := by
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv
  have hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminal.from X) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration X).mp hX
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := terminal.from X) k inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry p β i v hv W hW hI) k
      (terminal.from X) (terminal.from L) := ⟨terminal.hom_ext _ _⟩
  let t := sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry t, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection t, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      ((sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i) = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι_pre]
    change uncurry ((sq.lift ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ β))) = _
    rw [SSet.comp_const, SSet.const_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex v
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_parameter]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (k ≫ (sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv)) = W
    rw [← Category.assoc, sq.fac_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry_uncurry]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
