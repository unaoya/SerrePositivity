module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightSpanShape

/-!
概要：(3,2) の実正方形と三点 span の形状同型。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridRightSpanShapeIso : (horn 2 0 : SSet.{u}) ≅
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightLowerIndex.{u})
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridRightSpan (nerveEquiv v)) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso ≪≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanPastingIso.symm ≪≫
    PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
      (α := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanIndex.{u})
      (β := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCornerSpanIndex.{u}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanStandardOrderIso) ≪≫
    PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
      (α := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCornerSpanIndex.{u})
      (β := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightSpanIndex.{u})
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanStandardOrderIso.symm) ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridRightSpan

def excisionGridRightSquarePoint (i j : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := by
  let x : Fin 4 := ⟨i.val + 2, by omega⟩
  let y : Fin 4 := ⟨j.val + 1, by omega⟩
  exact ULift.up ⟨(x, y), by dsimp [x, y]; omega⟩

def excisionGridRightSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionGridRightSquarePoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        ((stdSimplex.objEquiv s.2).toOrderHom k),
      fun _ _ h ↦ ⟨Nat.add_le_add_right ((stdSimplex.objEquiv s.1).toOrderHom.monotone h) 2,
        Nat.add_le_add_right ((stdSimplex.objEquiv s.2).toOrderHom.monotone h) 1⟩⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
