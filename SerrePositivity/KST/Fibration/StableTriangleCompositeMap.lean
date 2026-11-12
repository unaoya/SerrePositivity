module
public import SerrePositivity.KST.Fibration.StableHomVertexRecovery
public import SerrePositivity.KST.Fibration.CoherentTriangleShortFaces

/-! # 指定 coherent 二単体の合成 path から、元の完全射の同じ合成を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の対象座標の等号と実完全射の異種等号は、同じ通常合成を保つ。 -/
theorem exactMap_comp_heq {A B C A' B' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (hC : C = C')
    {f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} {f' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A' B'} {g' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B' C'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (show A ⟶ C from (show A ⟶ B from f) ≫ (show B ⟶ C from g))
      (show A' ⟶ C' from (show A' ⟶ B' from f') ≫ (show B' ⟶ C' from g')) := by
  cases hA
  cases hB
  cases hC
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- 同じ元の一単体の等号は、回収した実完全射の異種等号を与える。 -/
theorem stableArrowExactMap_heq {a b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌} (h : a = b) :
    HEq (stableArrowExactMap a) (stableArrowExactMap b) := by cases h; rfl

/-- 元の二単体の同じ合成 path から回収する実完全射。 -/
def stableTriangleCompositeMap (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩) :=
  stableHomExactMap (coherentTriangleHomVertex s coherentTriangleFullPath)

/-- 元の合成 path の実完全射は、元の同じ二短辺から回収した実完全射の合成。 -/
theorem stableTriangleCompositeMap_eq_comp (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) :
    stableTriangleCompositeMap s = (show s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 2⟩ from
      stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s) ≫
        stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s)) := by
  have h := (congrArg (fun v => stableHomExactMap v)
    (coherentTriangleHomVertex_comp s coherentTriangleFirstPath coherentTriangleLastPath)).trans
      (stableHomExactMap_comp _ _)
  exact h.trans (congrArg₂ (fun (f : s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 1⟩)
    (g : s.obj ⟨ULift.up 1⟩ ⟶ s.obj ⟨ULift.up 2⟩) => f ≫ g)
    (congrArg (fun v => stableHomExactMap v) (coherentTriangleFirst_vertex s))
    (congrArg (fun v => stableHomExactMap v) (coherentTriangleLast_vertex s)))

/-- 元の二短辺が指定した完全射の同じ一単体なら、合成 path は元の合成を回収する。 -/
theorem stableTriangleCompositeMap_heq_of_faces (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌)
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 s = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge)
    (hg : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow g).edge) :
    HEq (stableTriangleCompositeMap s)
      (show A ⟶ C from (show A ⟶ B from f) ≫ (show B ⟶ C from g)) := by
  have hA : (s.obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = A :=
    congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})) hf
  have hB : (s.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = B :=
    congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})) hf
  have hC : (s.obj ⟨ULift.up 2⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = C :=
    congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})) hg
  have hF := (stableArrowExactMap_heq hf).trans (heq_of_eq (stableArrowExactMap_arrow f))
  have hG := (stableArrowExactMap_heq hg).trans (heq_of_eq (stableArrowExactMap_arrow g))
  exact (heq_of_eq (stableTriangleCompositeMap_eq_comp s)).trans
    (exactMap_comp_heq hA hB hC hF hG)

end SerrePositivity.KST.Fibration
