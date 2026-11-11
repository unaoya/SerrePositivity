module
public import SerrePositivity.KST.Fibration.PointSourceCosliceData
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftIntervalFatHomotopy

/-! # 元の可変終点 coslice 比較の、全時間での両端固定 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {A X : SSet.{u}} {x : X _⦋0⦌} {g : A ⟶ X}
  {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X} (d : PointSourceCosliceData x g F)

/-- 左の点は、元の比較ホモトピーの全時間で厳密に固定される。 -/
theorem PointSourceCosliceData.fixed_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ yonedaEquiv.symm x := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨z, t⟩
  have hh := congrArg (fun (m : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj n ⟶
    X.obj n) => m (Sum.inl z, t)) (NatTrans.congr_app d.fixed n)
  exact hh.trans (ConcreteCategory.congr_hom (NatTrans.congr_app d.fatLeft n) z)

/-- 右因子も、同じ可変終点図式の値に全時間で厳密に固定される。 -/
theorem PointSourceCosliceData.fixed_right :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h =
      fst A Δ[1] ≫ g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨z, t⟩
  have hh := congrArg (fun (m : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram (Δ[0] : SSet.{u}) A ⊗ Δ[1]).obj n ⟶
    X.obj n) => m (Sum.inr z, t)) (NatTrans.congr_app d.fixed n)
  exact hh.trans (ConcreteCategory.congr_hom (NatTrans.congr_app d.fatRight n) z)

end SerrePositivity.KST.Fibration
