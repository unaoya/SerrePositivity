module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-! # 固定した頂点上のホモトピーの成分

概要：ある頂点で定値なホモトピーは、h C の自然変換で恒等射の成分を与える。
方針：固定条件を一次単体で評価し、成分の辺が退化辺であることを示す。
規約：端点の対象の等号による輸送を Arrow の等号に含める。
使われ方：S4 の cofiber と suspension の比較の第一成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：頂点で定値な単体的ホモトピーの自然変換の成分は恒等射である。
方針：頂点の区間の一次単体で固定条件を評価し、辺の類を恒等辺と比較する。
規約：quasicategory 性は不要、端点の輸送を Arrow の等号で表す。
使われ方：suspension との比較で始点の恒等性を確認する。 -/
lemma homotopyNatTrans_fixedVertex_arrow {A X : SSet.{u}}
    (U : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (i : (Δ[0] : SSet.{u}) ⟶ A) (x : X _⦋0⦌)
    (hfix : (i ▷ (Δ[1] : SSet.{u})) ≫ U = snd Δ[0] Δ[1] ≫ SSet.const x) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans U).app (SSet.HomotopyCategory.mk (SSet.yonedaEquiv i))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  let a := stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 1)
  have hia : i.app (Opposite.op ⦋0⦌) a = SSet.yonedaEquiv i := by
    have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [ha, ← SSet.yonedaEquiv_comp, Category.id_comp]
  have he := congrArg (fun h : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ X ↦
    h.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hfix
  change U.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, hia] at he
  let e := ((SSet.Truncated.Edge.id (X := (truncation 2).obj A)
    (SSet.yonedaEquiv i)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map U)
  have heq : e.edge = (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge := by
    change U.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) (SSet.yonedaEquiv i)).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact he
  have hArrow := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) heq
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e) = _
  have hid := SSet.Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj X) x
  have hi := congrArg Arrow.mk hid
  exact hArrow.trans hi

/-- 概要：指定した両端の関手への自然変換も固定頂点で恒等射を与える。
方針：両端の等式で置き換え、固定頂点の成分の式を適用する。
規約：端点の型の輸送も含む。使われ方：実際の比較ホモトピーの成分。 -/
lemma homotopyNatTransOfEndpoints_fixedVertex_arrow {A X : SSet.{u}} {F G : A ⟶ X}
    (U : A ⊗ (Δ[1] : SSet.{u}) ⟶ X) (h₀ : SSet.ι₀ ≫ U = F) (h₁ : SSet.ι₁ ≫ U = G)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (x : X _⦋0⦌)
    (hfix : (i ▷ (Δ[1] : SSet.{u})) ≫ U = snd Δ[0] Δ[1] ≫ SSet.const x) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints U h₀ h₁).app
      (SSet.HomotopyCategory.mk (SSet.yonedaEquiv i))) =
        Arrow.mk (𝟙 (SSet.HomotopyCategory.mk x)) := by
  subst F G
  exact homotopyNatTrans_fixedVertex_arrow U i x hfix

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
