module
public import SerrePositivity.KST.Fibration.StableHomCompositionVertices
public import SerrePositivity.KST.Fibration.CoherentTriangleDiagonal

/-! # 元の Kan Hom の頂点から、同じ完全射と通常合成を厳密に回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の通常完全射の頂点から、同じ元の完全射を厳密に回収する。 -/
theorem stableHomExactMap_homEquiv' {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : A ⟶ B) :
    stableHomExactMap (SimplicialCategory.homEquiv' A B f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm
    ((stableHomAmbient A B).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' A B f)) = f.hom
  rw [stableHomAmbient_homEquiv']
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _

/-- 元の Kan Hom の任意の頂点を、回収した同じ完全射の頂点表示として読む。 -/
theorem stableHom_homEquiv'_ExactMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (v : (A ⟶[SSet.{u}] B) _⦋0⦌) :
    SimplicialCategory.homEquiv' A B (stableHomExactMap v) = v := by
  obtain ⟨f, rfl⟩ := (SimplicialCategory.homEquiv' A B).surjective v
  rw [stableHomExactMap_homEquiv']

/-- 元の全 Hom の合成頂点は、同じ二つの元の完全射の通常合成を回収する。 -/
theorem stableHomExactMap_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (v : (A ⟶[SSet.{u}] B) _⦋0⦌) (w : (B ⟶[SSet.{u}] C) _⦋0⦌) :
    stableHomExactMap ((eComp SSet A B C).app (Opposite.op ⦋0⦌) (v, w)) =
      (show A ⟶ C from (show A ⟶ B from stableHomExactMap v) ≫
        (show B ⟶ C from stableHomExactMap w)) := by
  obtain ⟨f, rfl⟩ := (SimplicialCategory.homEquiv' A B).surjective v
  obtain ⟨g, rfl⟩ := (SimplicialCategory.homEquiv' B C).surjective w
  rw [← simplicialHomVertex_comp, stableHomExactMap_homEquiv',
    stableHomExactMap_homEquiv', stableHomExactMap_homEquiv']

/-- 指定した coherent 一単体の元の Hom 頂点から回収した、同じ実完全射。 -/
def stableArrowExactMap (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩) :=
  stableHomExactMap (coherentArrowHomVertex a)

/-- 通常完全射の同じ coherent 一単体から、元の完全射を厳密に回収する。 -/
theorem stableArrowExactMap_arrow {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow f).edge = f := by
  change stableHomExactMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B f) 0) = f
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  exact stableHomExactMap_homEquiv' f

end SerrePositivity.KST.Fibration
