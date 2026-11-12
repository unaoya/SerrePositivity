module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseHomotopyDown

/-!
概要：ホモトピー圏の宇宙下降は元の単体集合の射の作用と可換。
方針：生成辺の下降の厳密な一致を関手の等式へ移す。
規約：指定射の類を保持。使われ方：相対前合成と小宇宙下降の指定比較の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 持ち上げた射による実辺の像を降ろすと元の射による像になる。 -/
lemma downTruncatedEdge_map {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y) :
    downTruncatedEdge (e.map ((truncation 2).map ((SSet.uliftFunctor.{v, u}).map f))) =
      (downTruncatedEdge e).map ((truncation 2).map f) := by
  apply Truncated.Edge.ext
  rfl

/-- 宇宙下降の関手は元の単体集合の射に関して厳密に自然。 -/
lemma universeHomotopyDown_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    universeHomotopyDown.{u, v} X ⋙ SSet.mapHomotopyCategory f =
      SSet.mapHomotopyCategory ((SSet.uliftFunctor.{v, u}).map f) ⋙ universeHomotopyDown Y := by
  apply Truncated.HomotopyCategory.functor_ext
    (F := universeHomotopyDown X ⋙ SSet.mapHomotopyCategory f)
    (G := SSet.mapHomotopyCategory ((SSet.uliftFunctor.{v, u}).map f) ⋙ universeHomotopyDown Y)
    (fun x => rfl)
  intro x y e
  simp only [Functor.comp_map, SSet.mapHomotopyCategory,
    Truncated.mapHomotopyCategory_homMk, universeHomotopyDown_map_homMk,
    eqToHom_refl, Category.id_comp, Category.comp_id, downTruncatedEdge_map]

/-- 指定頂点同型の下降は元の射による指定像と可換。 -/
lemma downVertexIso_map {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌} (e : VertexIso x y) (f : X ⟶ Y) :
    VertexIso.map (downVertexIso e) f =
      downVertexIso (VertexIso.map e ((SSet.uliftFunctor.{v, u}).map f)) := by
  rw [downVertexIso_eq_mapIso, downVertexIso_eq_mapIso]
  change (universeHomotopyDown X ⋙ SSet.mapHomotopyCategory f).mapIso e =
    (SSet.mapHomotopyCategory ((SSet.uliftFunctor.{v, u}).map f) ⋙
      universeHomotopyDown Y).mapIso e
  have hmap (F G : ((SSet.uliftFunctor.{v, u}).obj X).HomotopyCategory ⥤ Y.HomotopyCategory)
      (h : F = G) : HEq (F.mapIso e) (G.mapIso e) := by
    cases h
    rfl
  exact eq_of_heq (hmap _ _ (universeHomotopyDown_naturality f))

/-- 端点表示と指定同型の HEq を保って同じ実頂点同型を下降する。 -/
lemma downVertexIso_heq_of_heq {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : VertexIso x y) (e' : VertexIso x' y') (hx : x = x') (hy : y = y')
    (he : HEq e e') : HEq (downVertexIso e) (downVertexIso e') := by
  subst x'
  subst y'
  cases eq_of_heq he
  rfl

end SerrePositivity.InfinityCategories.F2
