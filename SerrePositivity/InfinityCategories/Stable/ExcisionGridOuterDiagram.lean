module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram

/-!
概要：full 格子の実 3×3 図式と中央・外側の四面の厳密比較。
方針：実際の長方形の貼り合わせと同じ図式の評価を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionGridOuterDiagramPoint (i j : Fin 3) : ExcisionGridIndex.{u} := by
  let x : Fin 4 := ⟨i.val + 1, by omega⟩
  let y : Fin 4 := ⟨j.val + 1, by omega⟩
  exact ULift.up ⟨(x, y), by dsimp [x, y]; omega⟩

def excisionGridOuterDiagram : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶
    nerve ExcisionGridIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionGridOuterDiagramPoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        ((stdSimplex.objEquiv s.2).toOrderHom k),
      fun _ _ h ↦ ⟨Nat.add_le_add_right ((stdSimplex.objEquiv s.1).toOrderHom.monotone h) 1,
        Nat.add_le_add_right ((stdSimplex.objEquiv s.2).toOrderHom.monotone h) 1⟩⟩ :
      Fin (n.unop.len + 1) →o ExcisionGridIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma excisionGridOuterDiagram_lowerLeft : grid22Face excisionGridOuterDiagram.{u} 2 2 =
    excisionGridCenterSquare ≫ nerveMap excisionGridCoreInclusion ≫
      nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridOuterDiagram_lowerRight : grid22Face excisionGridOuterDiagram.{u} 0 2 =
    excisionGridRightSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridOuterDiagram_upperLeft : grid22Face excisionGridOuterDiagram.{u} 2 0 =
    (β_ Δ[1] Δ[1]).hom ≫ excisionGridLeftSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridOuterDiagram_upperRight : grid22Face excisionGridOuterDiagram.{u} 0 0 =
    excisionGridFinalSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
