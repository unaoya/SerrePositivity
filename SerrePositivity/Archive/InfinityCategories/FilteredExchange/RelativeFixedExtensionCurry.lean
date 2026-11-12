module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：図式と部分族を固定する実円柱を、同じ相対延長空間の族へ移す。
方針：底固定の curry を部分族固定の fiber に持ち上げる。
規約：充填性や可縮性を仮定せず同じ実円柱を保持する。
使われ方：零面の実円柱を既存の指定比較と同じ空間へ入れる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 相対関手の定値頂点の族を展開すると元の定値図式を回収する。 -/
lemma relativeFunctorUncurry_const_vertex {A T E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (f : A ⟶ E) (hf : f ≫ p = b) :
    relativeFunctorUncurry
      (SSet.const (relativeFunctorVertex p b f hf) : T ⟶ relativeFunctorSpace p b) =
        fst A T ≫ f := by
  unfold relativeFunctorUncurry
  rw [SSet.const_comp]
  exact uncurry_const_functorVertex f

/-- 底と部分族を固定する実図式の族を元の相対延長空間へ curry する。 -/
def relativeFixedExtensionCurry {D A T E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (H : A ⊗ T ⟶ E)
    (hB : H ≫ p = fst A T ≫ b) (hV : (i ▷ T) ≫ H = fst D T ≫ v) :
    T ⟶ relativeFunctorExtensionSpace p b i v hv :=
  vertexFiberLift (relativeFunctorPre p b i) (relativeFunctorVertex p (i ≫ b) v hv)
    (relativeFunctorCurry H hB) (by
      apply relativeFunctorUncurry_injective p (i ≫ b)
      rw [relativeFunctorUncurry_pre, relativeFunctorUncurry_curry,
        relativeFunctorUncurry_const_vertex]
      exact hV)

/-- 同じ延長空間の族を展開すると元の実円柱そのものへ戻る。 -/
lemma relativeFixedExtensionCurry_uncurry {D A T E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (H : A ⊗ T ⟶ E)
    (hB : H ≫ p = fst A T ≫ b) (hV : (i ▷ T) ≫ H = fst D T ≫ v) :
    relativeFunctorUncurry (relativeFixedExtensionCurry p b i v hv H hB hV ≫
      relativeFunctorExtensionSpaceι p b i v hv) = H :=
  relativeFunctorUncurry_curry H hB

end SerrePositivity.InfinityCategories.F2
