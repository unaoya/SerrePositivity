module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.StronglySaturatedClosure

/-!
概要：元の辺の強飽和類への所属をホモトピー圏の合成関係で比較する。
方針：辺の類の合成関係から元の二単体を回収し、二対三則を使う。
規約：辺の代表を変更しても、同じ端点と射の類を保持する。
使われ方：HTT 5.5.4 の局所対象への置換と生成閉包の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open _root_.CategoryTheory MonoidalClosed _root_.SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HTT.Section5_5_4

/-- ホモトピー圏での合成関係を実現する、元の三辺を持つ二単体。 -/
def compStructOfHomotopyCategoryFac {X : SSet.{v}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    {e01 : Truncated.Edge (X := (truncation 2).obj X) x y}
    {e12 : Truncated.Edge (X := (truncation 2).obj X) y z}
    {e02 : Truncated.Edge (X := (truncation 2).obj X) x z}
    (h : Truncated.HomotopyCategory.homMk e01 ≫ Truncated.HomotopyCategory.homMk e12 =
      Truncated.HomotopyCategory.homMk e02) : Truncated.Edge.CompStruct e01 e12 e02 := by
  apply Truncated.Edge.CompStruct.ofHomotopyCategory₂Fac
  have hh := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X)).map) h
  simpa only [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
    Truncated.HomotopyCategory.lift_map_homMk] using hh

/-- 同じ端点で同じ射を表す二辺は、強飽和類への所属が一致する。 -/
lemma stronglySaturated_mem_iff_of_homMk_eq {X : SSet.{v}} [Quasicategory X]
    (smallShape : SSet.{u} → SSet.{v}) {S : Set (X _⦋1⦌)}
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape S)
    {x y : X _⦋0⦌} (e f : Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : Truncated.HomotopyCategory.homMk e = Truncated.HomotopyCategory.homMk f) :
    e.edge ∈ S ↔ f.edge ∈ S := by
  let i := Truncated.Edge.id (X := (truncation 2).obj X) y
  have hi : i.edge ∈ S := hS.1 i (by
    change IsIso (Truncated.HomotopyCategory.homMk i)
    dsimp only [i]
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance)
  let t : Truncated.Edge.CompStruct e i f := _root_.SerrePositivity.InfinityCategories.HTT.Section5_5_4.compStructOfHomotopyCategoryFac (by
    rw [Truncated.HomotopyCategory.homMk_id, Category.comp_id]
    exact h)
  exact ⟨fun he ↦ hS.2.2.2.1 t he hi, fun hf ↦ hS.2.2.2.2.2 t hi hf⟩

end SerrePositivity.InfinityCategories.HTT.Section5_5_4

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.4.6" (partial := component) "仮定：全小余極限を持つ準圏と強飽和辺集合（HTT と一致）。結論：全可逆辺の包含と、同じホモトピー圏の射を表す同端点の辺の所属不変性（明示された二つの結論に一致）。一般の retract に対する閉性はこの宣言には含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section5_5_4.stronglySaturated_mem_iff_of_homMk_eq
