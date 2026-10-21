module

public import SerrePositivity.InfinityCategories.F2.UniverseHomotopyDown
public import SerrePositivity.InfinityCategories.F2.VertexIsoTerminalEquality

/-!
概要：射の合成・宇宙下降・後合成の一つの関手の作用を、順次の指定像と照合する。
方針：ホモトピー圏の関手の合成則と既存 downVertexIso の指定値の等式を使う。
規約：元の同型の値を保持。使われ方：実終点評価から小さい fiber の関手への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定像の合成・下降・後合成は、同じ一つの関手の指定同型への作用に等しい。 -/
lemma universeHomotopyDown_composite_mapIso
    {K L : SSet.{max u v}} {X Y : SSet.{u}} [Quasicategory X]
    (f : K ⟶ L) (g : L ⟶ (SSet.uliftFunctor.{v, u}).obj X) (h : X ⟶ Y)
    {x y : K _⦋0⦌} (e : VertexIso x y) :
    (SSet.mapHomotopyCategory (f ≫ g) ⋙ universeHomotopyDown X ⋙
      SSet.mapHomotopyCategory h).mapIso e =
    VertexIso.map (downVertexIso (VertexIso.map (VertexIso.map e f) g)) h := by
  change VertexIso.map ((universeHomotopyDown X).mapIso (VertexIso.map e (f ≫ g))) h = _
  rw [← downVertexIso_eq_mapIso, ← vertexIso_map_comp]

end SerrePositivity.InfinityCategories.F2
