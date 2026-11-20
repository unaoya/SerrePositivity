module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseEvaluation
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows

/-!
概要：負次数延長したMoore反転も、第0項の同じ包含を保つ。
方針：延長射の指定成分と同型の両逆則を、元の零次包含則へ戻す。
規約：IS-W2 C01の既存構成の単位・係数移送則。
使われ方：HA 1.2.4、Tot錐の零次評価の合成の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory HomologicalComplex AlgebraicTopology
variable {C : Type*} [Category* C] [Abelian C]

/-- 延長した同じMoore反転の第0項は、指定延長同型と元の包含に両立する。 -/
theorem normalizedMooreReverse_extend_zero_inclusion (W : SimplicialObject C) :
    let N := (normalizedMooreComplex C).obj W
    let Nr := (normalizedMooreComplex C).obj (SimplicialObject.opFunctor.obj W)
    (extendMap (normalizedMooreReverse.app W) ComplexShape.embeddingDownNat).f 0 ≫
      (negativeChainRowIso N 0).hom ≫ (inclusionOfMooreComplexMap W).f 0 =
    (negativeChainRowIso Nr 0).hom ≫
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0 := by
  dsimp only
  erw [extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by rfl)]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, normalizedMooreReverse_zero_inclusion]
  rfl

end SerrePositivity.HomologicalAlgebra
