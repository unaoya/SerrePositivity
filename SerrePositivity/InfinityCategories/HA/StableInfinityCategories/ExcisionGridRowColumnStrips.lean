module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Strip3Pasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridFinalSuspension

/-!
概要：元の二頂点から対角頂点へ向かう実長方形の全単体の写像。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridRowStripPoint (i : Fin 4) (j : Fin 2) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := by
  let y : Fin 4 := ⟨j.val + 1, by omega⟩
  exact ULift.up ⟨(i, y), by dsimp [y]; omega⟩

def excisionGridRowStrip : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionGridRowStripPoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        ((stdSimplex.objEquiv s.2).toOrderHom k),
      fun _ _ h ↦ ⟨((stdSimplex.objEquiv s.1).toOrderHom.monotone h),
        Nat.add_le_add_right ((stdSimplex.objEquiv s.2).toOrderHom.monotone h) 1⟩⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

def excisionGridColumnStrip : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  excisionGridRowStrip ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetOrderIsoFunctor _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridTranspose)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
