module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRowColumnStrips

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
namespace SerrePositivity.InfinityCategories

lemma excisionGridRowStrip_first : strip3Square excisionGridRowStrip.{u} 3 2 =
    (β_ Δ[1] Δ[1]).hom ≫ pastingSquare excisionGridUpperRectangle 0 ≫
      nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridRowStrip_second : strip3Square excisionGridRowStrip.{u} 3 0 =
    excisionGridCenterSquare ≫ nerveMap excisionGridCoreInclusion ≫
      nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridRowStrip_third : strip3Square excisionGridRowStrip.{u} 0 0 =
    excisionGridRightSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_first : strip3Square excisionGridColumnStrip.{u} 3 2 =
    (β_ Δ[1] Δ[1]).hom ≫ pastingSquare excisionGridLowerRectangle 0 ≫
      nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_second : strip3Square excisionGridColumnStrip.{u} 3 0 =
    (β_ Δ[1] Δ[1]).hom ≫ excisionGridCenterSquare ≫
      nerveMap excisionGridCoreInclusion ≫ nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridColumnStrip_third : strip3Square excisionGridColumnStrip.{u} 0 0 =
    excisionGridLeftSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
