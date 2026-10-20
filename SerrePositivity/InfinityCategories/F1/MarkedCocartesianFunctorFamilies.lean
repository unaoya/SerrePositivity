module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionFamilies
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSquarePost

/-!
概要：指定辺を保つ相対関手の全パラメーターの族を、元の直積上の射と対応させる。
方針：相対 curry と uncurry を指定辺の条件へ制限する。
規約：パラメーター方向の全高次を保持する。
使われ方：指定された cocartesian 辺を保つ元の Hom の余極限への貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 各パラメーター頂点で指定辺を保つ元の射を、相対関手の族へ curry する。 -/
def markedCocartesianFunctorCurry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    (W : Set (A _⦋1⦌)) (F : A ⊗ T ⟶ E) (hF : F ≫ q = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), e ∈ W → IsCocartesianEdge q
      (F.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1))) :
    T ⟶ markedCocartesianFunctorSpace q a W :=
  fullSubcomplexLift _ (relativeFunctorCurry F hF) (by
    intro x
    have hv : ((relativeFunctorVertexEquiv q a).symm
        ((relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x)).val =
        lift (𝟙 A) (SSet.const x) ≫ F := by
      apply functorVertex_injective
      have hk := kanFunctorVertex_parameter (curry F) x
      rw [uncurry_curry] at hk
      exact ((functorVertexEquiv A E).apply_symm_apply _).trans hk.symm
    intro e he
    change IsCocartesianEdge q
      ((((relativeFunctorVertexEquiv q a).symm
        ((relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x)).val).app (Opposite.op ⦋1⦌) e)
    rw [hv]
    exact hc x e he)

/-- 指定辺を保つ族を、元の直積上の底上の図式へ展開する。 -/
def markedCocartesianFunctorUncurry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    {W : Set (A _⦋1⦌)} (g : T ⟶ markedCocartesianFunctorSpace q a W) : A ⊗ T ⟶ E :=
  relativeFunctorUncurry (g ≫ markedCocartesianFunctorInclusion q a W)

/-- 展開した元の族は指定した同じ底の図式に重なる。 -/
lemma markedCocartesianFunctorUncurry_projection {A T E B : SSet.{u}}
    {q : E ⟶ B} {a : A ⟶ B} {W : Set (A _⦋1⦌)}
    (g : T ⟶ markedCocartesianFunctorSpace q a W) :
    markedCocartesianFunctorUncurry g ≫ q = fst A T ≫ a :=
  relativeFunctorUncurry_projection _

/-- 構成した相対関手の族を展開すると、指定した同じ元の射を回収する。 -/
lemma markedCocartesianFunctorUncurry_curry {A T E B : SSet.{u}} {q : E ⟶ B} {a : A ⟶ B}
    (W : Set (A _⦋1⦌)) (F : A ⊗ T ⟶ E) (hF : F ≫ q = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), e ∈ W → IsCocartesianEdge q
      (F.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1))) :
    markedCocartesianFunctorUncurry (markedCocartesianFunctorCurry W F hF hc) = F :=
  relativeFunctorUncurry_curry F hF

/-- 元の図式への展開は、全パラメーターの相対関手の族を区別する。 -/
lemma markedCocartesianFunctorUncurry_injective {A T E B : SSet.{u}}
    (q : E ⟶ B) (a : A ⟶ B) (W : Set (A _⦋1⦌)) :
    Function.Injective (markedCocartesianFunctorUncurry
      (q := q) (a := a) (W := W) (T := T)) := by
  intro f g h
  apply (cancel_mono (fullSubcomplexOnVertices _ (markedCocartesianFunctorPredicate q a W)).ι).mp
  exact relativeFunctorUncurry_injective q a h

end SerrePositivity.InfinityCategories
