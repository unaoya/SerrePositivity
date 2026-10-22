module
public import SerrePositivity.InfinityCategories.Stable.Grid22Pasting
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSharedEdges
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridLowerRectanglePushout
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridUpperRectanglePushout

/-!
概要：core の実 3×3 図式と元の入力・三つの実四角形の同定。
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

def excisionGridCoreDiagram : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶
    nerve ExcisionGridCoreIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionGridCorePoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        ((stdSimplex.objEquiv s.2).toOrderHom k),
      fun _ _ h ↦ excisionGridCorePoint_le
        ((stdSimplex.objEquiv s.1).toOrderHom.monotone h)
        ((stdSimplex.objEquiv s.2).toOrderHom.monotone h)⟩ :
      Fin (n.unop.len + 1) →o ExcisionGridCoreIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma excisionGridCoreDiagram_lowerLeft : grid22Face excisionGridCoreDiagram.{u} 2 2 =
    excisionGridSquareShapeIso.inv ≫ nerveMap excisionGridSquareInclusion ≫
      nerveMap excisionGridSeedInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_lowerRight : grid22Face excisionGridCoreDiagram.{u} 0 2 =
    pastingSquare excisionGridLowerRectangle 0 := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_upperLeft : grid22Face excisionGridCoreDiagram.{u} 2 0 =
    (β_ Δ[1] Δ[1]).hom ≫ pastingSquare excisionGridUpperRectangle 0 := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_upperRight : grid22Face excisionGridCoreDiagram.{u} 0 0 =
    excisionGridCenterSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
