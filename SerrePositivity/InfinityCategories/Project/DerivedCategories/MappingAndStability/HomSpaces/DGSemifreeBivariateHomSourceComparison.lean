module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorFixedSecond
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeBivariateHomTargetComparison
/-!
概要：同じ二変数 D(R) 値 Hom の固定終域制限を、既存の反変 Hom と全関手同型で比較する。
方針：定値切断合成の零・単位の判定と同じ実直積写像を使う。
規約：全単体・全面・退化を保持する。使われ方：二変数 Hom と既存 Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped BigOperators _root_.Simplicial
variable (R : Type u) [CommRing R]
open CartesianMonoidalCategory
variable (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の固定終域における実全単体作用の照合。 -/
def dgSemifreeDerivedHomProductDGop_sourceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ))
        (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomProductDGopInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity R D Q) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomProductDGopInfinity
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorProductMap_first]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensor_sourceIso R D Q
/-- 元の固定終域における実全単体作用の照合。 -/
def dgSemifreeDerivedHomBivariate_sourceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op)
        (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariateInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity R D Q) := by
  have hbase : lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op)
      (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ⊗ₘ 𝟙 _) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫
        lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ))
          (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) := by
    rw [lift_map, comp_lift, Category.id_comp, Category.comp_id, Category.comp_id, SSet.comp_const]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariateInfinity _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity
  rw [← Category.assoc, hbase, Category.assoc]
  exact (dgSemifreeDerivedHomProductDGop_sourceIso R D Q).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories
