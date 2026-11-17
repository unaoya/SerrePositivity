module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の全分類が同じ底上の射へ与える像の端点の正規化を照合する。
方針：定義に含まれる同じ二つのEq.mpを外し、端点を含むArrowの等式へ戻す。
規約：元のleftStraighteningInfinityDiagramHomそのものを使う。
使われ方：同じ全変換の単位評価と実際のfiber射の照合。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma straighteningHomEqMp_heq_iff {α β : Sort u} (h : α = β) (a : α) {γ : Sort _} (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b := by cases h; rfl

/-- 元の同じ全straighteningが同じ底上の射へ与える像を、端点の等式の係数移送を除いて保持する。 -/
lemma leftStraighteningInfinityDiagramHom_heq {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    HEq (leftStraighteningInfinityDiagramHom p q f hf)
      ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) := by
  unfold leftStraighteningInfinityDiagramHom
  simp only [_root_.id_eq, straighteningHomEqMp_heq_iff]
  rfl
private lemma straighteningHomArrow_of_heq {D : Type u} [Category.{v} D]
    {a b a' b' : D} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : Arrow.mk f = Arrow.mk g := by
  subst a' b'
  cases h
  rfl

/-- 元の同じ底上の射の分類像は、端点を含むArrowとして元の図式の射と一致する。 -/
lemma leftStraighteningInfinityDiagramHom_arrow {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    Arrow.mk (leftStraighteningInfinityDiagramHom p q f hf) =
      Arrow.mk ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)) := by
  exact straighteningHomArrow_of_heq
    (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex p))
    (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_vertex q))
    (leftStraighteningInfinityDiagramHom_heq p q f hf)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
