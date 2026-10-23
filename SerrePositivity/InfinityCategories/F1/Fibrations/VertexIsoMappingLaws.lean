module

public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：指定された頂点同型の像の合成と、定値写像による恒等性。
方針：ホモトピー圏の関手性と、同じ辺の類の代表元で計算する。
規約：新しい辺や同型を選び直さず、指定同型の像自体を比較する。
使われ方：比較 Hom の fiber 内で作った同型の射影の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ頂点同型の二回の像は、合成した元の射による像。 -/
lemma VertexIso.map_comp {X Y Z : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : VertexIso x y) (f : X ⟶ Y) (g : Y ⟶ Z) :
    VertexIso.map (VertexIso.map e f) g = VertexIso.map e (f ≫ g) := by
  apply Iso.ext
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective x y e.hom
  change (mapHomotopyCategory g).map ((mapHomotopyCategory f).map e.hom) =
    (mapHomotopyCategory (f ≫ g)).map e.hom
  rw [← ha]
  rfl

/-- 定値写像による指定頂点同型の像は、同じ頂点の恒等同型。 -/
lemma VertexIso.map_const {X Y : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) (b : Y _⦋0⦌) :
    VertexIso.map e (SSet.const b : X ⟶ Y) =
      Iso.refl (SSet.HomotopyCategory.mk ((SSet.const b : X ⟶ Y).app _ x)) := by
  apply Iso.ext
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective x y e.hom
  change (mapHomotopyCategory (SSet.const b : X ⟶ Y)).map e.hom = 𝟙 _
  rw [← ha]
  change SSet.Truncated.HomotopyCategory.homMk
    (a.map ((truncation 2).map (SSet.const b : X ⟶ Y))) = 𝟙 _
  have he : a.map ((truncation 2).map (SSet.const b : X ⟶ Y)) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj Y)
        ((SSet.const b : X ⟶ Y).app (Opposite.op ⦋0⦌) x) := by
    apply SSet.Truncated.Edge.ext
    change PinchedHom.constant b 1 =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj Y) (PinchedHom.constant b 0)).edge
    rw [pinchedConstant_zero, pinchedConstant_one]
  rw [he]
  exact SSet.Truncated.HomotopyCategory.homMk_id _

/-- 同じ射の表示を等式で変更した像は、指定された端点の等号で移送される。 -/
lemma VertexIso.map_congr {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (e : VertexIso x y) {f g : X ⟶ Y} (h : f = g) :
    VertexIso.map e f =
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : X ⟶ Y ↦ t.app (Opposite.op ⦋0⦌) x) h)) ≪≫
      VertexIso.map e g ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun t : X ⟶ Y ↦ t.app (Opposite.op ⦋0⦌) y) h))).symm := by
  subst g
  simp

end SerrePositivity.InfinityCategories
