module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated

/-! # 八面体を作る二つの長方形

概要：合成射の cofiber 比較とその右面の cofiber を同時に構成し、最後の三角形の所属を示す。
方針：右面を転置して零対象を付加し、二つの接続射の合成式を使う。
規約：Mathlib の Octahedron 全体の構成は別途必要。使われ方：TR4 の幾何学的な代表。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：合成する二射の cofiber と、それらの間の cofiber を構成する二長方形。
方針：最初の長方形の右面の転置を次の長方形の左面として保持する。
規約：指定した元の列と底辺二単体を保つ。使われ方：八面体の四つの三角形の同時表示。 -/
structure CofiberOctahedronDiagram {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X)
    (τ : (Δ[2] : SSet.{u}) ⟶ X) where
  first : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberCompositionRectangle t τ
  second : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle
    ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare first.diagram 0)

/-- 概要：cofiber 列と適合する合成二単体から八面体の二長方形図式が存在する。
方針：合成射の比較長方形を選び、その右面の転置へ零対象を付加する。
規約：外側の余極限の存在は追加仮定しない。使われ方：TR4 の代表図式の存在。 -/
lemma nonempty_cofiberOctahedronDiagram {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (τ : (Δ[2] : SSet.{u}) ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ) :
    Nonempty (CofiberOctahedronDiagram t τ) := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberCompositionRectangle t ht τ h
  exact ⟨⟨r, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenPushoutCofiberRectangle _
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).1 r.right_isPushout)⟩⟩

/-- 概要：八面体の最後の列の第一辺は二つの cofiber を結ぶ最初の長方形の上辺。
方針：第二長方形の共有辺を左面の等号と転置で戻す。
規約：単体的な辺の厳密な等号。使われ方：最後の三角形の第一射を m₁ と同定する。 -/
lemma CofiberOctahedronDiagram.last_firstEdge {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.second.rightZeroTriangle.square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 0 = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge, d.second.left_eq]
  rfl

/-- 概要：二つ目の元の射の cofiber 列の第一辺は最初の長方形の右下の辺。
方針：外側と左面の左辺の一致を転置して戻す。
規約：単体的な辺の厳密な等号。使われ方：元の二つ目の射の cofiber の照合。 -/
lemma CofiberOctahedronDiagram.next_firstEdge {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : CofiberOctahedronDiagram t τ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.second.outerZeroTriangle.square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0 := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.second.diagram 1 = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge, d.second.left_eq]
  rfl

/-- 概要：最後の cofiber 比較の始点成分は元の列の第二射。
方針：始点成分を第二長方形の下辺とし、共有辺で元の列の右辺へ戻す。
規約：端点は Arrow の等号に含める。使われ方：最後の第三射の式を δ₂₃ と v₁₂ の合成で読む。 -/
lemma CofiberOctahedronDiagram.last_source_arrow {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : CofiberOctahedronDiagram t τ) :
    Arrow.mk d.second.sourceHom =
      Arrow.mk t.hoShortComplex.g := by
  apply d.second.comparisonHom_source_arrow.trans
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge]
  apply congrArg SSet.yonedaEquiv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.first.diagram 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ t.square
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge, d.first.left_eq]

/-- 概要：二長方形から得る最後の三角形は合成表示した第三射でも distinguished。
方針：右面の cofiber 三角形の所属で第三射を接続射の合成式に置き換える。
規約：第一・第二射は実際の右面の辺。使われ方：八面体の最後の三角形の所属。 -/
lemma CofiberOctahedronDiagram.lastTriangle_mem {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X} {τ : (Δ[2] : SSet.{u}) ⟶ X} (d : CofiberOctahedronDiagram t τ) :
    Triangle.mk d.second.rightZeroTriangle.hoShortComplex.f
      d.second.rightZeroTriangle.hoShortComplex.g
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.second.outerZeroTriangle d.second.outer_isCofiber).mor₃ ≫
        (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map
          d.second.sourceHom) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles
    d.second.rightZeroTriangle d.second.right_isCofiber
  change Triangle.mk d.second.rightZeroTriangle.hoShortComplex.f
    d.second.rightZeroTriangle.hoShortComplex.g
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle d.second.rightZeroTriangle d.second.right_isCofiber).mor₃ ∈ _ at h
  rw [d.second.triangle_connecting_comp] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
