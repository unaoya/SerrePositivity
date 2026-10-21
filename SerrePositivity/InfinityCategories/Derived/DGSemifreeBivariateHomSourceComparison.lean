module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorFixedSecond
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeBivariateHomTargetComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory
open scoped BigOperators Simplicial
variable (R : Type u) [CommRing R]
open CartesianMonoidalCategory
variable (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の固定終域における実全単体作用の照合。 -/
def dgSemifreeDerivedHomProductDGop_sourceIso (Q : SemifreeDGModules R D) :
    FunctorIso
      (lift (𝟙 (dgNerve R (SemifreeDGModules R D)ᵒᵖ))
        (SSet.const (Y := dgModuleDerivedInfinityCategory R D)
        (Simplex.vertex Q)) ≫ dgSemifreeDerivedHomProductDGopInfinity R D)
      (dgSemifreeDerivedHomSourceDGopInfinity R D Q) := by
  unfold dgSemifreeDerivedHomProductDGopInfinity
  rw [← Category.assoc, dgNerveTensorProductMap_first]
  exact dgSemifreeDerivedHomTensor_sourceIso R D Q
/-- 元の固定終域における実全単体作用の照合。 -/
def dgSemifreeDerivedHomBivariate_sourceIso (Q : SemifreeDGModules R D) :
    FunctorIso
      (lift (𝟙 (dgModuleDerivedInfinityCategory R D).op)
        (SSet.const (Y := dgModuleDerivedInfinityCategory R D)
        (Simplex.vertex Q)) ≫ dgSemifreeDerivedHomBivariateInfinity R D)
      (dgSemifreeDerivedContravariantHomInfinity R D Q) := by
  have hbase : lift (𝟙 (dgModuleDerivedInfinityCategory R D).op)
      (SSet.const (Y := dgModuleDerivedInfinityCategory R D)
        (Simplex.vertex Q)) ≫
      ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom ⊗ₘ 𝟙 _) =
      (dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫
        lift (𝟙 (dgNerve R (SemifreeDGModules R D)ᵒᵖ))
          (SSet.const (Y := dgModuleDerivedInfinityCategory R D)
        (Simplex.vertex Q)) := by
    rw [lift_map, comp_lift, Category.id_comp, Category.comp_id, Category.comp_id, SSet.comp_const]
  unfold dgSemifreeDerivedHomBivariateInfinity dgSemifreeDerivedContravariantHomInfinity
  rw [← Category.assoc, hbase, Category.assoc]
  exact (dgSemifreeDerivedHomProductDGop_sourceIso R D Q).precomp
    (dgNerveOppositeIso R (SemifreeDGModules R D)).hom

end SerrePositivity.InfinityCategories
