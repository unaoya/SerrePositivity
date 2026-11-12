module

public import SerrePositivity.KST.Spectra.SequenceRelativeTracedTriangles

/-!
概要：相対帰納構成の制限区間と構造像の区間を、元の同じパラメータ族で計算する。
方針：端点表示を変更しても保持する path 欄と、懸垂・後合成の元の式を取り出す。
規約：具体的な係数を展開しない。使われ方：上下の実合成三角形の面の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra

/-- 元の区間の辺を Yoneda で戻すと、同じ区間族そのもの。 -/
lemma PointedMapping.VerticalPath.edge_yonedaEquiv_symm
    {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : T ⟶ E}
    (P : PointedMapping.VerticalPath p f g) :
    SSet.yonedaEquiv.symm P.edge.edge = P.path := Equiv.symm_apply_apply _ _

namespace KanSequence
variable {X Y Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom Y Z) (hq : ∀ n, SSet.modelCategoryQuillen.J.rlp (q.app n).right)
  (b : Hom X Z) (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hb : ∀ n, f n ≫ q.app n = b.app n)
  (h : ∀ n, PointedMapping.VerticalPath (q.app (n + 1))
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))


/-- 構造射への制限の区間族は、元の次段比較区間への同じ前合成。 -/
lemma relativeTracedRestrictionPath_pre (n : ℕ) :
    (relativeTracedRestrictionPath hX q hq b f hb h n).path =
      (relativeTracedRectifyComparison hX q hq b f hb h (n + 1)).path ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space).right := rfl

/-- 前段比較の構造像の区間族は、同じ懸垂と後合成を施した族そのもの。 -/
lemma relativeTracedStepPath_path (n : ℕ) (s : RelativeTracedRectificationStage q b f n) :
    (relativeTracedStepPath q b f n s).path = s.comparison.path ≫
      (suspensionHom (X.level n).space (Y.level n).space).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)).right := rfl

end KanSequence
end SerrePositivity.KST.Spectra
