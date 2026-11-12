module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonExt

/-! # 頂点上の fiber の射と定値射

概要：頂点上の fiber の h の射は基底で恒等射になる。
方針：射を辺で表し、定値射の像が退化辺であることを計算する。
規約：端点の表示は Arrow の等号で輸送する。
使われ方：S3 の対象比較同型と S4 の標準比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：定値射は h の任意の射を固定した頂点の恒等射に送る。
方針：辺の代表を取り、像の一次単体を退化辺と比較する。
規約：始域は quasicategory。使われ方：fiber の射の基底への像。 -/
lemma stableHoConst_map_arrow {A X : SSet.{u}} [Quasicategory A] (x : X _⦋0⦌)
    {a b : A _⦋0⦌} (f : SSet.HomotopyCategory.mk a ⟶ SSet.HomotopyCategory.mk b) :
    Arrow.mk ((hoFunctor.map (SSet.const x : A ⟶ X)).toFunctor.map f) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective a b f
  let d := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have h : (e.map ((truncation 2).map (SSet.const x : A ⟶ X))).edge = d.edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 = d.edge
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x
  have he := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (e.map ((truncation 2).map (SSet.const x : A ⟶ X))) d h
  have hid := SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X) x
  exact he.trans (congrArg Arrow.mk hid)

/-- 概要：頂点上の fiber の h の射を基底に送るとその頂点の恒等射となる。
方針：fiber の包含の後の射影が定値射であることを使う。
規約：fiber の quasicategory 性のみを要求する。使われ方：対象比較の始点成分。 -/
lemma vertexFiberHo_projection_arrow {E B : SSet.{u}} (p : E ⟶ B) (x : B _⦋0⦌)
    [Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x)] {a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌}
    (f : SSet.HomotopyCategory.mk a ⟶ SSet.HomotopyCategory.mk b) :
    Arrow.mk ((hoFunctor.map p).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x)).toFunctor.map f)) =
        Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p x) f).trans (stableHoConst_map_arrow x f)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
