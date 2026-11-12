module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnStrips

/-!
概要：二つの長方形の三面と元の実六面の厳密同定。
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

lemma excisionGridRowStrip_first : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip.{u} 3 2 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUpperRectangle 0 ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridRowStrip_second : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip.{u} 3 0 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridRowStrip_third : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip.{u} 0 0 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_first : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip.{u} 3 2 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle 0 ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_second : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip.{u} 3 0 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_third : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip.{u} 0 0 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLeftSquare := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
