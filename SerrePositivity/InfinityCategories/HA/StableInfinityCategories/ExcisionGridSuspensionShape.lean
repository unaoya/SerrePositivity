module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex

/-!
概要：四つの実 suspension 模型を同じ全単体族にまとめる単調写像。
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

def excisionGridSuspensionIndexMap : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) →o
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} where
  toFun p := by
    let x : Fin 4 := ⟨if p.1.1 = 0 then p.2.1.val else p.2.2.val + 2, by
      split_ifs <;> omega⟩
    let y : Fin 4 := ⟨if p.1.2 = 0 then p.2.2.val else p.2.1.val + 2, by
      split_ifs <;> omega⟩
    exact ULift.up ⟨(x, y), by dsimp [x, y]; split_ifs <;> omega⟩
  monotone' := by
    intro p q h
    have ha := h.1.1
    have hb := h.1.2
    have hi := h.2.1
    have hj := h.2.2
    constructor
    · change (if p.1.1 = 0 then p.2.1.val else p.2.2.val + 2) ≤
        (if q.1.1 = 0 then q.2.1.val else q.2.2.val + 2)
      split_ifs <;> omega
    · change (if p.1.2 = 0 then p.2.2.val else p.2.1.val + 2) ≤
        (if q.1.2 = 0 then q.2.2.val else q.2.1.val + 2)
      split_ifs <;> omega

def excisionGridSuspensionShape :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1]) ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} where
  app n := ↾fun s ↦
    (excisionGridSuspensionIndexMap.comp
      (((stdSimplex.objEquiv s.1.1).toOrderHom.prod
        (stdSimplex.objEquiv s.1.2).toOrderHom).prod
        ((stdSimplex.objEquiv s.2.1).toOrderHom.prod
          (stdSimplex.objEquiv s.2.2).toOrderHom))).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

def excisionGridSuspensionAt (i j : Fin 2) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  lift (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))
    (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) ≫
      excisionGridSuspensionShape

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
