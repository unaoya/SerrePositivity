module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCorePoint

/-!
概要：比較格子の下側長方形への全単体に自然な写像。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridLowerRectangle : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        (((stdSimplex.objEquiv s.2).toOrderHom k).castSucc),
      fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint_le
        ((stdSimplex.objEquiv s.1).toOrderHom.monotone h)
        ((stdSimplex.objEquiv s.2).toOrderHom.monotone h)⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
