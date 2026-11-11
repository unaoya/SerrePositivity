module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStructureCounitTrace
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointPastedBoundary

/-!
概要：同じ上下三角形を保つ合成正方形を counit 座標へ移し、元の非定数境界の像を計算する。
方針：内部 Hom の交換と counit の同じ後合成を正方形全体へ施す。
規約：始点境界の収縮は未主張。使われ方：元の評価との比較による全列ホモトピーの構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u})

/-- 構造 Hom の区間を、元のパラメータと二重懸垂源の counit 座標へ移す同じ射。 -/
def kanAdjointStructureCounitMap (A : PointedSimplicialSet.{u}) (n : ℕ) :
    PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space ⟶
      PointedObject.basedHom A (PointedObject.basedHom
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)) (Y.level (n + 2)).space) :=
  (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
    (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 2)).space)).hom ≫
      PointedObject.basedHomMap A
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)

variable {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 元の合成正方形全体を、同じ counit 座標へ移した実ホモトピー。 -/
def kanAdjointRelativeTracedPastedCounitSquare (n : ℕ) :
    SSet.Homotopy
      ((stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n) ≫
        (kanAdjointStructureCounitMap X Y A n).right)
      ((stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n) ≫
        (kanAdjointStructureCounitMap X Y A n).right) where
  h := (kanAdjointRelativeTracedPastedSquare X Y φ j n).h ≫
    (kanAdjointStructureCounitMap X Y A n).right
  h₀ := by rw [← Category.assoc, (kanAdjointRelativeTracedPastedSquare X Y φ j n).h₀]; rfl
  h₁ := by rw [← Category.assoc, (kanAdjointRelativeTracedPastedSquare X Y φ j n).h₁]; rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 像の始点境界は、元の二段構造から始まる同じ実 counit 区間の族そのもの。 -/
lemma kanAdjointRelativeTracedPastedCounitSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedPastedCounitSquare X Y φ j n).h =
      (kanAdjointStructureCounitInterval X Y φ n).path := by
  change SquareAdjustment.leftSide ≫ ((kanAdjointRelativeTracedPastedSquare X Y φ j n).h ≫
    (kanAdjointStructureCounitMap X Y A n).right) = _
  rw [← Category.assoc, kanAdjointRelativeTracedPastedSquare_start]
  have he := kanAdjointTracedStructureCounitInterval_path X Y φ n
  change ((kanAdjointTracedStructureInterval X Y φ n).path ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 2)).space)).hom.right) ≫
      (PointedObject.basedHomMap A
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)).right = _ at he
  change (kanAdjointTracedStructureInterval X Y φ n).path ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 2)).space)).hom.right ≫
      (PointedObject.basedHomMap A
        (kanLoopCounit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 2)).space)).right) = _
  simpa only [Category.assoc] using he

/-- 同じ正方形の終点境界は、元の厳密化した構造頂点の counit 像で全体が一定。 -/
lemma kanAdjointRelativeTracedPastedCounitSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointRelativeTracedPastedCounitSquare X Y φ j n).h =
      SSet.const ((kanAdjointStructureCounitMap X Y A n).right.app _
        (PointedMapping.familyVertex
          (PointedSimplicialSet.circle.{u} ◁ (kanAdjointRelativeTracedParameterHom X Y φ j).app n ≫
            (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n))) := by
  change SquareAdjustment.rightSide ≫ ((kanAdjointRelativeTracedPastedSquare X Y φ j n).h ≫
    (kanAdjointStructureCounitMap X Y A n).right) = _
  rw [← Category.assoc, kanAdjointRelativeTracedPastedSquare_finish, SSet.const_comp]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
