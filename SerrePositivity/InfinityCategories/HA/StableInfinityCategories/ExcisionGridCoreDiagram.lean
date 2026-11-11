module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Grid22Pasting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSharedEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerRectanglePushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridUpperRectanglePushout

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridCoreDiagram : (Δ[2] : SSet.{u}) ⊗ Δ[2] ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint ((stdSimplex.objEquiv s.1).toOrderHom k)
        ((stdSimplex.objEquiv s.2).toOrderHom k),
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

lemma excisionGridCoreDiagram_lowerLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face excisionGridCoreDiagram.{u} 2 2 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareShapeIso.inv ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareInclusion ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_lowerRight : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face excisionGridCoreDiagram.{u} 0 2 =
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle 0 := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_upperLeft : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face excisionGridCoreDiagram.{u} 2 0 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUpperRectangle 0 := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridCoreDiagram_upperRight : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face excisionGridCoreDiagram.{u} 0 0 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> apply Subtype.ext <;>
    apply ULift.ext <;> apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
