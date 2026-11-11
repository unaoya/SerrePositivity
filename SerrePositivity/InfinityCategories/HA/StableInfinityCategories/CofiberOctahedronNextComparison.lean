module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangleHoMap
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TransposedPastingComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonIdentity

/-! # 八面体の合成射から次の射への比較

概要：合成射の cofiber から二つ目の射の cofiber への比較を作り、三成分を辺と照合する。
方針：第一長方形の外側から右面へ進み、第二長方形の左から外側への転置比較と合成する。
規約：端点の表示の違いは Arrow に保持する。使われ方：八面体の第二の三角形の射と可換式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：第二長方形の左面を転置すると第一長方形の右面となる。
方針：保持した左面の等号と二回の転置を計算する。
規約：単体的な射の厳密な等号。使われ方：二つの比較の厳密な合成。 -/
lemma CofiberOctahedronDiagram.nextComparison_start {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 2 =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0 := by
  rw [d.second.left_eq]
  rfl

/-- 概要：第一長方形の右面から次の射の cofiber 列への実際のホモトピー。
方針：第二長方形の左から外側への比較を転置し、先頭の四角形の等号を移す。
規約：終点は二つ目の射の cofiber 列。使われ方：合成射の cofiber の第二比較。 -/
def CofiberOctahedronDiagram.rightToNextHomotopy {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0) d.second.outerZeroTriangle.square where
  h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy d.second.diagram)).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy d.second.diagram)).h₀.trans d.nextComparison_start
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy d.second.diagram)).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (β_ (Δ[1] : SSet.{u}) Δ[1]).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy d.second.diagram)).rel

/-- 概要：右面から次の列への比較は底辺の各頂点を固定する。
方針：転置した比較の固定式を先頭の四角形の等号で移す。
規約：実際の道の等号。使われ方：始点と中間成分の恒等性。 -/
lemma CofiberOctahedronDiagram.rightToNextHomotopy_bottom {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) (j : Fin 2) :
    ((stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      d.rightToNextHomotopy.h = snd Δ[0] Δ[1] ≫
        SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0) j 0) := by
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.transposedPastingLeftToOuterHomotopy_bottom d.second.diagram j).trans
    (congrArg (fun F => snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F j 0))
      d.nextComparison_start)

/-- 概要：右面から次の列への比較の底辺の二成分は恒等射。
方針：固定頂点の成分を関手圏のホモトピー類の評価へ移す。
規約：端点の表示は Arrow の等号に含める。使われ方：合成の始点と中間成分の消去。 -/
lemma CofiberOctahedronDiagram.rightToNextHomotopy_bottom_arrow {X : SSet.{u}}
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ)
    (j : Fin 2) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X j 0).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d.rightToNextHomotopy))) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0) j 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyNatTrans_fixedVertex_arrow d.rightToNextHomotopy.h
    (stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0) j 0) (d.rightToNextHomotopy_bottom j)
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ j.rev ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) j 0 := by
    fin_cases j <;> apply Prod.ext <;> decide
  rw [hi] at h
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow d.rightToNextHomotopy _).trans h

/-- 概要：右面から次の列への比較の終点成分は第二長方形の右上の辺。
方針：転置した比較の右上の道を指定した辺の類と比較する。
規約：端点の輸送は Arrow に含める。使われ方：二つ目の cofiber 間の射。 -/
lemma CofiberOctahedronDiagram.rightToNextHomotopy_target_arrow {X : SSet.{u}}
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d.rightToNextHomotopy))) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoTop (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 0)) := by
  have hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.transposedPastingLeftToOuterHomotopy_target d.second.diagram
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow_of_vertexPath d.rightToNextHomotopy
    (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 0) hp
  have hi : SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
    apply Prod.ext <;> decide
  rw [hi] at h
  exact h.trans (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 0)))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow _) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge _).symm)

/-- 概要：合成射の cofiber 列から二つ目の射の cofiber 列への関手圏の h の比較。
方針：第一長方形の外側から右面への比較と、右面から次の列への比較を合成する。
規約：三角形の対象と接続射は構成済みのもの。使われ方：八面体の第二の比較。 -/
def CofiberOctahedronDiagram.nextComparisonHom {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.first.outerZeroTriangle.square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.second.outerZeroTriangle.square) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom d.first.diagram ≫
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d.rightToNextHomotopy)

/-- 概要：合成した比較の始点成分は元の第一射。
方針：第二因子の恒等成分を消して第一長方形の下辺を照合する。
規約：端点の表示を Arrow に保持。使われ方：八面体の第四の可換式の始点条件。 -/
lemma CofiberOctahedronDiagram.nextComparison_source_arrow {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map d.nextComparisonHom) =
      Arrow.mk t.hoShortComplex.f := by
  dsimp only [nextComparisonHom]
  rw [Functor.map_comp]
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableArrow_comp_of_right_identity _ _ (d.rightToNextHomotopy_bottom_arrow 0)).trans
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom_source_arrow d.first.diagram).trans
    (congrArg (fun F => Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom F)) d.first.left_eq)

/-- 概要：合成した比較の中間成分は恒等射。
方針：第二因子の恒等成分を消し、第一因子の右下の固定条件を使う。
規約：端点表示の違いを許す。使われ方：八面体の第三の可換式の中間条件。 -/
lemma CofiberOctahedronDiagram.nextComparison_middle_arrow {X : SSet.{u}}
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 0).map d.nextComparisonHom) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex d.first.outerZeroTriangle.square 1 0)) := by
  dsimp only [nextComparisonHom]
  rw [Functor.map_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableArrow_comp_of_right_identity _ _ (d.rightToNextHomotopy_bottom_arrow 1)).trans
    (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom_middle d.first.diagram))

/-- 概要：合成した比較の終点成分は最後の列の第二射。
方針：第一因子の恒等成分を消し、第二因子の上辺を転置した列の右辺と照合する。
規約：端点の表示を Arrow に保持。使われ方：八面体の最後の三角形の第二射との一致。 -/
lemma CofiberOctahedronDiagram.nextComparison_target_arrow {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map d.nextComparisonHom) =
      Arrow.mk d.second.rightZeroTriangle.hoShortComplex.g := by
  dsimp only [nextComparisonHom]
  rw [Functor.map_comp]
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableArrow_comp_of_left_identity _ _
    (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterToRightHom_target d.first.diagram))).trans
  apply d.rightToNextHomotopy_target_arrow.trans
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
  rfl

/-- 概要：合成射の cofiber 三角形から二つ目の射の cofiber 三角形への射。
方針：合成した関手圏の h の比較を三角形の射へ移す。
規約：第三の可換式には接続射の自然性を含む。使われ方：八面体の第二の三角形の射。 -/
def CofiberOctahedronDiagram.nextTriangleMorphism {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.first.outerZeroTriangle d.first.outer_isCofiber ⟶
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.second.outerZeroTriangle d.second.outer_isCofiber :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangleHoMap _ _ d.first.outer_isCofiber d.second.outer_isCofiber d.nextComparisonHom

/-- 概要：二つ目の比較は懸垂に値を取る接続射と可換。
方針：関手圏の h の射に接続射の自然性を適用する。
規約：始点・終点成分は上で辺と照合したもの。使われ方：八面体の第四の可換式。 -/
lemma CofiberOctahedronDiagram.nextConnecting_comm {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram t τ) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map d.nextComparisonHom ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d.second.outerZeroTriangle d.second.outer_isCofiber =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d.first.outerZeroTriangle d.first.outer_isCofiber ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map d.nextComparisonHom) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_naturality _ _ d.first.outer_isCofiber d.second.outer_isCofiber
    d.nextComparisonHom

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
