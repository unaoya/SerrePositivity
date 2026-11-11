module
public import SerrePositivity.KST.Fibration.WeakStringGappedNaturality

/-! # 元の object S(W 列) 二重単体集合と相対 S の交換の厳密同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 列次数を固定すると、元の object S と相対 S の実単体の行が厳密に同型。 -/
def weakStringObjectRelativeRowIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (m : ℕ) :
    objectSConstruction (weakStringCategory q ⦋m⦌) ≅
      relativeSimplicialSConstruction q.hom ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋m⦌) :=
  NatIso.ofComponents (fun n => Equiv.toIso (weakStringGappedSimplexEquiv q n.unop.len m)) (by
    intro n l θ
    apply ConcreteCategory.hom_ext
    intro v
    change SSet.yonedaEquiv (weakStringGappedRelativeMap q
      ((sMap (weakStringCategory q ⦋m⦌) θ.unop.toOrderHom).app (Opposite.op ⦋0⦌) v)) = _
    rw [weakStringGappedRelativeMap_sMap, SSet.yonedaEquiv_comp]
    rfl)

/-- 全列次数・全 S 次数の作用を保つ、元の二重単体集合の厳密な交換同型。 -/
def weakStringObjectRelativeIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringStableSimplicial q ⋙ objectSConstructionFunctor ≅
      (relativeSimplicialSConstruction q.hom).flip :=
  NatIso.ofComponents (fun m => weakStringObjectRelativeRowIso q m.unop.len) (by
    intro m l θ
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro v
    change SSet.yonedaEquiv (weakStringGappedRelativeMap q
      (((sEndofunctor n.unop.len).map (weakStringExactMap q θ.unop)).val.app
        (Opposite.op ⦋0⦌) v)) = _
    rw [weakStringGappedRelativeMap_reindex, ← SSet.yonedaEquiv_naturality]
    rfl)

end SerrePositivity.KST.Fibration
