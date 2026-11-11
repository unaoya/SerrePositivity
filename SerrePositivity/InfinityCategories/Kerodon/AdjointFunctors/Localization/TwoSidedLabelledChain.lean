module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 二方向の要素圏の元の射列の両端ラベルによる回収

概要：要素圏の全射列は元の底の射列と終点の左ラベル・始点の右ラベルから復元される。
方針：左ラベルは終点から反変に、右ラベルは始点から共変に移す。
規約：元の全頂点と全射を厳密に保持する。
使われ方：DK §9.5・10.6の元の二方向 bar の行の余積表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Type u) (G : W ⥤ Type u)

lemma element_ext (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G) (hb : X.base = Y.base)
    (hl : HEq X.left Y.left) (hr : HEq X.right Y.right) : X = Y := by
  cases X
  cases Y
  cases hb
  cases eq_of_heq hl
  cases eq_of_heq hr
  rfl

lemma eqToHom_base {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element.base h) := by
  cases h
  rfl

variable {n : ℕ} (c : ComposableArrows W n)
  (a : F.obj (op (c.obj (Fin.last n)))) (b : G.obj (c.obj 0))

def lift : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G) n where
  obj i := ⟨c.obj i, F.map (c.map (homOfLE (Fin.le_last i))).op a,
    G.map (c.map (homOfLE (Fin.zero_le i))) b⟩
  map {i j} h :=
    { base := c.map h
      left := by
        change F.map (c.map h).op (F.map (c.map (homOfLE (Fin.le_last j))).op a) = _
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, ← c.map_comp]
        rfl
      right := by
        change G.map (c.map h) (G.map (c.map (homOfLE (Fin.zero_le i))) b) = _
        rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← c.map_comp]
        rfl }
  map_id i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G _ _ (c.map_id i)
  map_comp h k := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G _ _ (c.map_comp h k)

lemma lift_projection : lift F G c a b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection F G = c := rfl

lemma reconstruct (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G) n) :
    lift F G (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection F G) (e.obj (Fin.last n)).left (e.obj 0).right = e := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · exact element_ext F G _ _ rfl
      (heq_of_eq (e.map (homOfLE (Fin.le_last i))).left)
      (heq_of_eq (e.map (homOfLE (Fin.zero_le i))).right)
  · intro i j h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G
    simp [lift, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_comp_base, eqToHom_base, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection]

def chainEquiv (n : ℕ) : ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G) n ≃
    (Σ c : ComposableArrows W n, F.obj (op (c.obj (Fin.last n))) × G.obj (c.obj 0)) where
  toFun e := ⟨e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection F G, (e.obj (Fin.last n)).left, (e.obj 0).right⟩
  invFun c := lift F G c.1 c.2.1 c.2.2
  left_inv := reconstruct F G
  right_inv c := by
    rcases c with ⟨c, a, b⟩
    change (⟨c, ((lift F G c a b).obj (Fin.last n)).left,
      ((lift F G c a b).obj 0).right⟩ :
      Σ c : ComposableArrows W n, F.obj (op (c.obj (Fin.last n))) × G.obj (c.obj 0)) = _
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Prod.ext
    · change F.map (c.map (homOfLE (Fin.le_last (Fin.last n)))).op a = a
      rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) from Subsingleton.elim _ _,
        c.map_id, op_id, F.map_id, types_id_apply]
    · change G.map (c.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) b = b
      rw [show homOfLE (Fin.zero_le (0 : Fin (n + 1))) = 𝟙 0 from Subsingleton.elim _ _,
        c.map_id, G.map_id, types_id_apply]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain
