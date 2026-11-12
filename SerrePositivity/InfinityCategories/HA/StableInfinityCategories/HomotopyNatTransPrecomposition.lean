module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass

/-! # 単体的自然変換の前合成と成分

概要：単体的ホモトピーの前合成は h の自然変換の成分の前合成を与える。
方針：頂点の恒等辺の像を恒等辺と照合する。
規約：端点輸送を Arrow の等号で扱う。使われ方：完全関手間の自然変換の接続射との両立。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：両端の指定による輸送は成分の Arrow を変えない。
方針：両端の等式で置き換える。
規約：quasicategory 性は不要。使われ方：自然変換の成分の計算。 -/
lemma homotopyNatTransOfEndpoints_app_arrow {X Y : SSet.{u}} {F G : X ⟶ Y}
    (H : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) (h₀ : SSet.ι₀ ≫ H = F) (h₁ : SSet.ι₁ ≫ H = G)
    (x : X _⦋0⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H h₀ h₁).app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans H).app (SSet.HomotopyCategory.mk x)) := by
  subst F G
  rfl

/-- 概要：ホモトピーを前合成してから頂点で評価することは像の頂点での評価と一致。
方針：恒等辺は単体的な射で恒等辺に写ることを使う。
規約：値域への追加仮定は不要。使われ方：図式へ制限した自然変換の成分。 -/
lemma homotopyNatTrans_precomp_app_arrow {A X Y : SSet.{u}} (i : A ⟶ X)
    {F G : X ⟶ Y} (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp i H).h).app
      (SSet.HomotopyCategory.mk x)) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans H.h).app
      (SSet.HomotopyCategory.mk (i.app (Opposite.op ⦋0⦌) x))) := by
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  have hi := congrArg SSet.Truncated.Edge.edge
    (SSet.Truncated.Edge.map_id x ((truncation 2).map i))
  change H.h.app (Opposite.op ⦋1⦌)
      (i.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (i.app (Opposite.op ⦋0⦌) x)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  change i.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge =
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (i.app (Opposite.op ⦋0⦌) x)).edge at hi
  exact congrArg (fun a ↦ H.h.app (Opposite.op ⦋1⦌) (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hi

/-- 概要：指定両端を持つ単体的自然変換の前合成も成分の前合成を与える。
方針：両端の輸送を消して前合成の成分式を使う。
規約：Arrow の等号に端点の表示を含める。使われ方：cofiber 列へ制限した自然変換。 -/
lemma homotopyNatTransOfEndpoints_precomp_app_arrow {A X Y : SSet.{u}} (i : A ⟶ X)
    {F G : X ⟶ Y} (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp i H).h
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp i H).h₀ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp i H).h₁).app
      (SSet.HomotopyCategory.mk x)) =
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints H.h H.h₀ H.h₁).app
      (SSet.HomotopyCategory.mk (i.app (Opposite.op ⦋0⦌) x))) :=
  (homotopyNatTransOfEndpoints_app_arrow _ _ _ _).trans
    ((homotopyNatTrans_precomp_app_arrow i H x).trans
      (homotopyNatTransOfEndpoints_app_arrow _ _ _ _).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
