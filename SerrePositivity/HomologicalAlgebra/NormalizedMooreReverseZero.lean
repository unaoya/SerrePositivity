module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreReverse

/-!
概要：正規化Moore反転は、第0項の指定包含の後では恒等となる。
方針：反転の零次符号は1、Moore射影P∞の第0項も恒等であることを使う。
規約：IS-W2 C01の既存Moore分裂の単位・係数移送則。
使われ方：HA 1.2.4、指定Tot錐の標準脚の零次評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory AlgebraicTopology
variable {C : Type*} [Category* C] [Abelian C]

/-- 指定Moore反転の第0項は、同じ包含を通して元の第0項へ戻る。 -/
theorem normalizedMooreReverse_zero_inclusion (W : SimplicialObject C) :
    (normalizedMooreReverse.app W).f 0 ≫ (inclusionOfMooreComplexMap W).f 0 =
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0 := by
  dsimp only [normalizedMooreReverse, NatTrans.comp_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f,
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  simp only [alternatingFaceReverseNatIso, NatIso.ofComponents_hom_app,
    alternatingFaceReverseIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    alternatingFaceReverseDegreeIso, alternatingFaceReverseSign, one_smul,
    DoldKan.PInfty_f, DoldKan.P_f_0_eq]
  change (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0 ≫
    𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]

end SerrePositivity.HomologicalAlgebra
