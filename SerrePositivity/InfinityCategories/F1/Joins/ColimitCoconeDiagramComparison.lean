module

public import SerrePositivity.InfinityCategories.F1.Joins.ColimitCoconeProjection
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：同型な下方図式の指定余極限余錐を、全余錐の関手同型で比較する。
方針：普遍余錐全体の射影の同値を通して下方の同型を持ち上げる。
規約：両方の元の余錐と元の下方図式を固定し、余錐の頂点だけの比較に弱めない。
使われ方：Ind の点ごとの filtered 補完を元の実普遍四角形へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定された余極限余錐を、普遍余錐全体の実頂点とする。 -/
def colimitCoconeDiagramVertex {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) :
    (colimitCocones K X) _⦋0⦌ :=
  ⟨functorVertex c.val, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, CategoryTheory.Functor.map_id_apply]
    exact hc.initialBoundaryLifting⟩

/-- 普遍余錐の実頂点の下方は、指定した元の図式そのもの。 -/
lemma colimitCoconeDiagramVertex_projection {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) :
    (colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) (colimitCoconeDiagramVertex c hc) =
      functorVertex p := by
  change functorVertex (joinInl K (Δ[0] : SSet.{u}) ≫ c.val) = _
  rw [c.property]

/-- 同型な下方図式の元の指定余極限余錐は、全余錐の関手空間で同型である。 -/
def colimitCoconeDiagramIso {K X : SSet.{u}} [Quasicategory X]
    (h : ∀ p : K ⟶ X, HasColimit p) {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (e : FunctorIso p q) : FunctorIso c.val d.val := by
  have : TrivialKanFibration (colimitCoconeProjection K X) :=
    colimitCoconeProjection_trivialKanFibration h
  have : Quasicategory (colimitCocones K X) :=
    quasicategory_of_innerFibration (colimitCoconeProjection K X)
  let w := qCatEquivalenceOfTrivialKanFibration (colimitCoconeProjection K X)
  let x := colimitCoconeDiagramVertex c hc
  let y := colimitCoconeDiagramVertex d hd
  have eb : VertexIso ((colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) x)
      ((colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) y) := by
    dsimp only [x, y]
    rw [colimitCoconeDiagramVertex_projection, colimitCoconeDiagramVertex_projection]
    exact e
  have ex := w.homInvIso.app x
  have ey := w.homInvIso.app y
  have et : VertexIso x y := ex.symm ≪≫ eb.map w.inv ≪≫ ey
  exact et.map (relativeInitialVertices (coconeRestriction K X)).ι

end SerrePositivity.InfinityCategories
