module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeEdgeCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSectionSpace

/-!
概要：join錐の指定脚は、同じcoslice切断の第0単体を評価した辺。
方針：切断のcurryの定義を第0単体で読み、頂点輸送は等式で消去する。
規約：IS-W2 C01の既存構成の評価則。元の一次単体を保持する。
使われ方：HA 1.2.4、Tot錐の標準脚の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial

/-- 元の錐の脚は、同じ正規化coslice切断の頂点での値。 -/
theorem joinCone_section_leg {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (v : K _⦋0⦌) (z : X _⦋0⦌) (h : c.vertex = z) :
    (derivedConeLeg c v).edge = SSet.yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫
        (((coherentConeCosliceSection c ≫ eqToHom (congrArg
          (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
          (Opposite.op ⦋0⦌) v).val)) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
