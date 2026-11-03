module

public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.TerminalMap
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.CatInfinity.SpecifiedLimitConeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.KanIntervalCospan
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.KanIntervalPullbackTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

/-!
概要：任意の Kan cospan の区間による path 引き戻しを、元の図式の native な極限錐にする。
方針：指定円柱で輸送した錐を標準の Kan 図式上に表示する。
規約：元の二射に fibration 性は要求しない。
使われ方：𝒮 の引き戻しと filtered 余極限の比較から fibration 仮定を外す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：元の任意の cospan 上の区間による path 引き戻し錐。
方針：定値切断の指定円柱で戻した錐の表示を正規化する。
規約：輸送の全錐のホモトピーは intervalPullbackStrictConeTransport が保持する。 -/
def intervalPullbackCone (f : X ⟶ Y) (g : Z ⟶ Y) : JoinCone (kanDiagramCoherentNerve
    (kanPullbackDiagram f g)) :=
  (intervalPullbackStrictConeTransport f g).cone.cast (strictCoherentDiagram_eq_kanDiagram _)

/-- 概要：区間の引き戻し錐は元の任意の cospan の実際の ∞ 極限。
方針：指定円柱に沿う極限錐の輸送の普遍性を使う。
規約：両射の fibration 性は不要。使われ方：一般の二射の引き戻し模型。 -/
lemma intervalPullbackCone_isLimit (f : X ⟶ Y) (g : Z ⟶ Y) :
    IsLimitCone (intervalPullbackCone f g) :=
  (intervalPullbackStrictConeTransport f g).isLimit.cast _

/-- 概要：元の cospan の極限頂点は実際の二段の path 引き戻し。
方針：輸送の頂点の等式を置換後の元の頂点の式に合成する。
規約：台の模型との厳密な同定は intervalPullbackKanObject_obj。使われ方：filtered 比較。 -/
lemma intervalPullbackCone_vertex (f : X ⟶ Y) (g : Z ⟶ Y) :
    (intervalPullbackCone f g).vertex = spaceInfinityVertex (intervalPullbackKanObject f g) := by
  rw [intervalPullbackCone, JoinCone.vertex_cast,
    (intervalPullbackStrictConeTransport f g).vertex_eq, intervalPullbackReplacementCone_vertex]
  exact (spaceInfinityVertex_eq_coherent _).symm

end SerrePositivity.InfinityCategories.F2
