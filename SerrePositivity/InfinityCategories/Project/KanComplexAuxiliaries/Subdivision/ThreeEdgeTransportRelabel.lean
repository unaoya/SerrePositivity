module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ThreeEdgeTransport

/-!
概要：三辺輸送の一次単体を保ったまま端点表示を照合し、閉じた輸送辺の恒等性を判定する。
方針：辺の同じ単体から端点等式を回収し、元の二つの三角形の面をそのまま使う。
規約：輸送辺を選び直さない。使われ方：境界の帰納三角形からトレース恒等性を導く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.ThreeEdgeTransport
end SerrePositivity.KST.Spectra.ThreeEdgeTransport
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

variable {Z : SSet.{u}} {x a y b : Z _⦋0⦌}
  {left : Z.Edge x a} {middle : Z.Edge x y} {right : Z.Edge y b}

/-- 元の単体を持つ辺へ端点表示を直しても、対角辺と二つの三角形の単体は変更しない。 -/
def relabel (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right) {x' a' y' b' : Z _⦋0⦌}
    (left' : Z.Edge x' a') (middle' : Z.Edge x' y') (right' : Z.Edge y' b')
    (hl : left.edge = left'.edge) (hm : middle.edge = middle'.edge)
    (hr : right.edge = right'.edge) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left' middle' right' := by
  have hx : x = x' := left.src_eq.symm.trans ((congrArg (Z.δ 1) hl).trans left'.src_eq)
  have ha : a = a' := left.tgt_eq.symm.trans ((congrArg (Z.δ 0) hl).trans left'.tgt_eq)
  have hb : b = b' := right.tgt_eq.symm.trans ((congrArg (Z.δ 0) hr).trans right'.tgt_eq)
  exact {
    diagonal := SSet.Edge.mk D.diagonal.edge
      (D.diagonal.src_eq.trans hx) (D.diagonal.tgt_eq.trans hb)
    transported := SSet.Edge.mk D.transported.edge
      (D.transported.src_eq.trans ha) (D.transported.tgt_eq.trans hb)
    first := {
      simplex := D.first.simplex
      d₀ := D.first.d₀.trans hr
      d₁ := D.first.d₁
      d₂ := D.first.d₂.trans hm }
    second := {
      simplex := D.second.simplex
      d₀ := D.second.d₀
      d₁ := D.second.d₁
      d₂ := D.second.d₂.trans hl } }

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (relabel)


/-- 端点表示を直しても、元の輸送辺の一次単体は厳密に同じ。 -/
lemma relabel_transported_edge (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right)
    {x' a' y' b' : Z _⦋0⦌} (left' : Z.Edge x' a') (middle' : Z.Edge x' y')
    (right' : Z.Edge y' b') (hl : left.edge = left'.edge) (hm : middle.edge = middle'.edge)
    (hr : right.edge = right'.edge) :
    (D.relabel left' middle' right' hl hm hr).transported.edge = D.transported.edge := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (relabel_transported_edge)


/-- 三辺自身が同じ対角辺を持つ実三角形をなすなら、閉じた輸送辺の類は恒等射。 -/
lemma transported_homMk_eq_id [KanComplex Z] {x y b : Z _⦋0⦌}
    {left : Z.Edge x b} {middle : Z.Edge x y} {right : Z.Edge y b}
    (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right) (t : SSet.Edge.CompStruct middle right left) :
    SSet.HomotopyCategory.homMk D.transported = 𝟙 (SSet.HomotopyCategory.mk b) := by
  let leftIso : IsIso (SSet.HomotopyCategory.homMk left) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers left.toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex left.toTruncated)
  apply (cancel_epi (SSet.HomotopyCategory.homMk left)).1
  rw [Category.comp_id, D.trace, SSet.HomotopyCategory.homMk_comp_homMk t]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (transported_homMk_eq_id)


/-- 同じ一次単体を持つ閉辺の恒等性は、基点の表示を変更しても変わらない。 -/
lemma loop_identity_congr {x y : Z _⦋0⦌} {e : Z.Edge x x} {f : Z.Edge y y}
    (h : e.edge = f.edge)
    (hf : SSet.HomotopyCategory.homMk f = 𝟙 (SSet.HomotopyCategory.mk y)) :
    SSet.HomotopyCategory.homMk e = 𝟙 (SSet.HomotopyCategory.mk x) := by
  have hx : x = y := e.src_eq.symm.trans ((congrArg (Z.δ 1) h).trans f.src_eq)
  subst y
  have he : e = f := SSet.Edge.ext h
  rw [he]
  exact hf

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport export _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries (loop_identity_congr)


end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
