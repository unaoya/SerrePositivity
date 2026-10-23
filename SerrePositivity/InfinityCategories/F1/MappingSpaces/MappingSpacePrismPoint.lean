module

public import SerrePositivity.InfinityCategories.F1.Coherent.PrismCutCoordinates
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：一点をパラメーターとする左右の join 区間比較を、元の標準一単体で計算する。
方針：零単体の一意性と join の円柱の標準座標を使う。
規約：右と左の区間比較の零単体の辺を厳密に同定する。
使われ方：右 Hom の pointed 比較を、指定した点の同じ coslice の辺へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 一点パラメーターの右 join 区間は、二点 join の標準同型で元の時間座標に戻る。 -/
lemma rightMappingSpacePrism_point_hom :
    rightMappingSpacePrism (Δ[0] : SSet.{u}) ≫ (joinStdSimplexIso 0 0).hom =
      fst (Δ[1] : SSet.{u}) Δ[0] := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, z⟩
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (((joinStdSimplexIso 0 0).hom.app (Opposite.op ⦋n⦌)
    ((joinCylinderMap Δ[0] Δ[0]).app (Opposite.op ⦋n⦌)
      ((z, t), PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n))) i).val = (t i).val
  rw [joinCylinderMap_stdSimplex_val]
  have hz := (z i).isLt
  have ht := (t i).isLt
  change (if (t i).val = 0 then (z i).val else 0 + 1 + 0) = (t i).val
  split_ifs <;> omega

/-- 一点パラメーターの右区間比較は、時間座標を二点 join に戻す標準射そのもの。 -/
lemma rightMappingSpacePrism_point :
    rightMappingSpacePrism (Δ[0] : SSet.{u}) =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).inv := by
  apply (cancel_mono (joinStdSimplexIso 0 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, rightMappingSpacePrism_point_hom]

/-- 一点パラメーターでは、左右の join 区間比較は厳密に同じ射。 -/
lemma leftMappingSpacePrism_point :
    leftMappingSpacePrism (Δ[0] : SSet.{u}) = rightMappingSpacePrism Δ[0] := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, z⟩
  rw [stdSimplex_zero_eq_constant z]
  rfl

end SerrePositivity.InfinityCategories
