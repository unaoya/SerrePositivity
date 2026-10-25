module

public import SerrePositivity.InfinityCategories.Core.LimitProjectionExistence
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：同型な下方図式の指定極限錐を、全錐の関手同型で比較する。
方針：普遍錐全体の射影の同値を通して下方の同型を持ち上げる。
規約：両方の元の錐と元の下方図式を固定し、錐の頂点だけの比較に弱めない。
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

/-- 指定された極限錐を、普遍錐全体の実頂点とする。 -/
def limitConeDiagramVertex {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    (limitCones K X) _⦋0⦌ :=
  ⟨functorVertex c.val, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, CategoryTheory.Functor.map_id_apply]
    exact terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc⟩

/-- 普遍錐の実頂点の下方は、指定した元の図式そのもの。 -/
lemma limitConeDiagramVertex_projection {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    (limitConeProjection K X).app (Opposite.op ⦋0⦌) (limitConeDiagramVertex c hc) =
      functorVertex p := by
  change functorVertex (joinInr (Δ[0] : SSet.{u}) K ≫ c.val) = _
  rw [c.property]

/-- 同型な下方図式の元の指定極限錐は、全錐の関手空間で同型である。 -/
def limitConeDiagramIso {K X : SSet.{u}} [Quasicategory X]
    (h : ∀ p : K ⟶ X, HasLimit p) {p q : K ⟶ X}
    (c : JoinCone p) (d : JoinCone q) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (e : FunctorIso p q) : FunctorIso c.val d.val := by
  have : TrivialKanFibration (limitConeProjection K X) :=
    limitConeProjection_trivialKanFibration h
  have : Quasicategory (limitCones K X) :=
    quasicategory_of_innerFibration (limitConeProjection K X)
  let w := qCatEquivalenceOfTrivialKanFibration (limitConeProjection K X)
  let x := limitConeDiagramVertex c hc
  let y := limitConeDiagramVertex d hd
  have eb : VertexIso ((limitConeProjection K X).app (Opposite.op ⦋0⦌) x)
      ((limitConeProjection K X).app (Opposite.op ⦋0⦌) y) := by
    dsimp only [x, y]
    rw [limitConeDiagramVertex_projection, limitConeDiagramVertex_projection]
    exact e
  have ex := w.homInvIso.app x
  have ey := w.homInvIso.app y
  have et : VertexIso x y := ex.symm ≪≫ eb.map w.inv ≪≫ ey
  exact et.map (relativeTerminalVertices (coneRestriction K X)).ι

end SerrePositivity.InfinityCategories
