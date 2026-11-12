module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices

/-!
概要：底と初期値を固定する実際の族を、相対延長空間への族へ戻す。
方針：底上で curry した族を、初期制限の fiber へ厳密に持ち上げる。
規約：円柱や高次のパラメータを選び直さず、同じ raw な族を回収する。
使われ方：輸送比較円柱を可縮な延長空間内で比較し、高次の整合性を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 底と初期値を固定するパラメータ族を、同じ相対延長空間への射として表す。 -/
def fixedExtensionCurry {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry W hW) (by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p (i ≫ β)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, hI]
      change _ = uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ β) v hv) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ β)))
      rw [SSet.const_comp]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex v).symm)

/-- 相対延長空間への持ち上げは、包含後に元の相対 curry そのものになる。 -/
lemma fixedExtensionCurry_ι {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    fixedExtensionCurry p β i v hv W hW hI ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry W hW := by
  dsimp only [fixedExtensionCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 延長空間へ戻した同じ族を展開すると、元の raw な族を厳密に回収する。 -/
lemma fixedExtensionCurry_uncurry {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      (fixedExtensionCurry p β i v hv W hW hI ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) =
        W := by
  rw [fixedExtensionCurry_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]

/-- 延長空間の族をパラメータ頂点で評価すると、同じ頂点で制限した実際の延長になる。 -/
lemma fixedExtensionCurry_vertex {A D L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) (x : L _⦋0⦌) :
    (fixedExtensionCurry p β i v hv W hW hI).app _ x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β i v hv
        ⟨lift (𝟙 A) (SSet.const x) ≫ W,
          by rw [Category.assoc, hW, ← Category.assoc, lift_fst, Category.id_comp], by
            rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.parameterVertex_naturality, Category.assoc, hI,
              ← Category.assoc, lift_fst, Category.id_comp]⟩ := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurry_vertex p β W hW x

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
