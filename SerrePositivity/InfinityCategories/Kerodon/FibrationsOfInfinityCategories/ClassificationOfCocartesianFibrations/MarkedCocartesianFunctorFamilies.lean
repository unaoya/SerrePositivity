module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost

/-!
概要：指定辺を保つ相対関手の全パラメーターの族を、元の直積上の射と対応させる。
方針：相対 curry と uncurry を指定辺の条件へ制限する。
規約：パラメーター方向の全高次を保持する。
使われ方：指定された cocartesian 辺を保つ元の Hom の余極限への貼り合わせ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 各パラメーター頂点で指定辺を保つ元の射を、相対関手の族へ curry する。 -/
def markedCocartesianFunctorCurry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    (W : Set (A _⦋1⦌)) (F : A ⊗ T ⟶ E) (hF : F ≫ q = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), e ∈ W → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (F.app (Opposite.op ⦋1⦌) (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q a W :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF) (by
    intro x
    have hv : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x)).val =
        lift (𝟙 A) (SSet.const x) ≫ F := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
      have hk := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorVertex_parameter (curry F) x
      rw [uncurry_curry] at hk
      exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).apply_symm_apply _).trans hk.symm
    intro e he
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q a).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x)).val).app (Opposite.op ⦋1⦌) e)
    rw [hv]
    exact hc x e he)

/-- 指定辺を保つ族を、元の直積上の底上の図式へ展開する。 -/
def markedCocartesianFunctorUncurry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    {W : Set (A _⦋1⦌)} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q a W) : A ⊗ T ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q a W)

/-- 展開した元の族は指定した同じ底の図式に重なる。 -/
lemma markedCocartesianFunctorUncurry_projection {A T E B : SSet.{u}}
    {q : E ⟶ B} {a : A ⟶ B} {W : Set (A _⦋1⦌)}
    (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q a W) :
    markedCocartesianFunctorUncurry g ≫ q = fst A T ≫ a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

/-- 構成した相対関手の族を展開すると、指定した同じ元の射を回収する。 -/
lemma markedCocartesianFunctorUncurry_curry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    (W : Set (A _⦋1⦌)) (F : A ⊗ T ⟶ E) (hF : F ≫ q = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), e ∈ W → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q
      (F.app (Opposite.op ⦋1⦌) (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    markedCocartesianFunctorUncurry (markedCocartesianFunctorCurry W F hF hc) = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry F hF

/-- 元の図式への展開は、全パラメーターの相対関手の族を区別する。 -/
lemma markedCocartesianFunctorUncurry_injective {A T E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (W : Set (A _⦋1⦌)) :
    Function.Injective (markedCocartesianFunctorUncurry
      (q := q) (a := a) (W := W) (T := T)) := by
  intro f g h
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPredicate q a W)).ι).mp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective q a h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
