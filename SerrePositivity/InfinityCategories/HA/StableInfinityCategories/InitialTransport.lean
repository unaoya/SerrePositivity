module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointHornJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OuterHornDuality

/-! # 始対象と余極限の同型不変性

概要：始対象性と余極限性はホモトピー圏の同型で保たれる。
方針：最初の可逆辺を持つ外側ホーンを充填する。
規約：Core の終対象の証明の双対をここに置く。使われ方：S3 の選択の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：零対象性はホモトピー圏の同型に沿って保たれる。
方針：始対象性と終対象性をそれぞれ同型で移す。
規約：頂点の等号は要求しない。使われ方：fiber/cofiber の零角の置換。 -/
lemma IsZeroVertex.of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex y :=
  ⟨hx.1.of_vertexIso e, hx.2.of_vertexIso e⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroVertex (of_vertexIso)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
