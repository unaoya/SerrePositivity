module
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreReverse

/-!
概要：指定 Moore 反転比較の成分を元の非正規化複体で評価する。
方針：正規化射影と包含の合成を PInfty に戻し、零次数の恒等式を使う。
規約：零次数の評価を変えず、正次数の反転符号は保持する。
使われ方：HA 1.2.4、G10 の指定錐の標準脚の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Abelian C]

/-- 指定反転射を包含後に評価すると、同じ符号同型と PInfty の合成になる。 -/
@[reassoc]
theorem normalizedMooreReverse_inclusion (W : SimplicialObject C) :
    normalizedMooreReverse.app W ≫ inclusionOfMooreComplexMap W =
      inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W) ≫
        (alternatingFaceReverseIso W).hom ≫ DoldKan.PInfty := by
  change (inclusionOfMooreComplexMap _ ≫ (alternatingFaceReverseIso W).hom ≫
    DoldKan.PInftyToNormalizedMooreComplex W) ≫ _ = _
  simp only [Category.assoc,
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]

/-- 零次数では反転比較は元の頂点の評価を厳密に保つ。 -/
theorem normalizedMooreReverse_zero_inclusion (W : SimplicialObject C) :
    (normalizedMooreReverse.app W).f 0 ≫ (inclusionOfMooreComplexMap W).f 0 =
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0 := by
  have h := congrArg (fun f => f.f 0) (normalizedMooreReverse_inclusion W)
  simp only [HomologicalComplex.comp_f, alternatingFaceReverseIso_hom_f_zero,
    DoldKan.PInfty_f_0, Category.comp_id] at h
  erw [Category.comp_id] at h
  exact h

end SerrePositivity.HomologicalAlgebra
