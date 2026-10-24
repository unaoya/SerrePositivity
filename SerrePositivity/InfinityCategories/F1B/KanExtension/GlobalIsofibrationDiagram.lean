module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.IsofibrationCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalLiftingDiagram

/-!
概要：inner 性と可逆辺の持ち上げの下での厳密な相対 Kan 図式の組み立て。
方針：isofibration の二条件から右持ち上げ条件を供給して既存の構成を適用する。
規約：元の図式と標的の大域図式を厳密に保つ。
使われ方：Kerodon Proposition 7.3.6.7 の相対的な存在部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：isofibration 上の局所相対余極限を厳密な大域図式へ組み立てる。
方針：内ホーン充填と指定可逆辺の持ち上げから圏論的同値の右持ち上げを導く。
規約：元・標的の図式は厳密に固定し、全 fiber の標準 U 余極限性も保つ。
使われ方：全部分圏からの相対 Kan 拡張の写像空間の制限定理の存在入力。 -/
lemma exists_kanGlobalRelative_diagram_with_relative_colimits_of_isofibration
    {K C D E : SSet.{u}} [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) [InnerFibration U]
    (hU : SerrePositivity.InfinityCategories.F1B.InvertibleTargetLifting U) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧ z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧ H ≫ U = H₀ ∧
        ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanRelativeJoinFiberCocone p c H) := by
  have hl : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U := by
    intro A B i hm hi
    exact SerrePositivity.InfinityCategories.F1B.equivalenceLifting_of_innerFibration_of_targetLifting U hU i hm hi
  exact exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting
    p U hl F H₀ hFU hlocal

end SerrePositivity.InfinityCategories.F1B
