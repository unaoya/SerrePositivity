module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：相対延長空間の普遍的な全延長は、全パラメータで同じ元の初期値を保持する。
方針：初期値固定の fiber の包含式を uncurry する。
規約：一頂点での評価に弱めない。使われ方：元の全三単体の第一辺の実現証拠。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 全延長をそのまま展開すると、元の全初期値を全選択で厳密に回収する。 -/
lemma relativeExtensionUniversal_initial {A D E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) :
    (i ▷ relativeFunctorExtensionSpace p b i v hv) ≫
      relativeFunctorUncurry (relativeFunctorExtensionSpaceι p b i v hv) =
        fst D (relativeFunctorExtensionSpace p b i v hv) ≫ v := by
  have h := congrArg (fun z => z ≫ vertexFiberι ((ihom D).map p)
    (functorVertex (i ≫ b))) (relativeFunctorExtensionSpaceι_pre p b i v hv)
  simp only [Category.assoc, relativeFunctorPre_ι, SSet.const_comp] at h
  change relativeFunctorExtensionSpaceι p b i v hv ≫
    vertexFiberι ((ihom A).map p) (functorVertex b) ≫ (pre i).app E =
      SSet.const (functorVertex v) at h
  rw [relativeFunctorUncurry, ← uncurry_pre_app, Category.assoc, h,
    uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2
