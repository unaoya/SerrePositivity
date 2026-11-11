module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionShape
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnStrips

/-!
概要：四つの実パラメーター制限を同じ suspension 四角形と厳密比較する。
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

lemma excisionGridSuspensionAt_source : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u} 0 0 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram 1 1 ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫
      nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridSuspensionAt_column : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u} 1 0 =
    (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip 1 1 := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridSuspensionAt_row : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u} 0 1 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip 1 1 := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridSuspensionAt_target : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u} 1 1 =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram 1 1 := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
