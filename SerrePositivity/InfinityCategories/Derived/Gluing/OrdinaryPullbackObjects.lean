module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.Size
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackEquivalenceSubcomplex
/-!
概要：元 dg gluing の中で、同じ導来 augmentation が可逆な対象の充満 dg 部分圏を取る。
方針：正本の全矢印族で対象条件を指定し、Hom 複体・単位・合成をそのまま制限する。
規約：元の二対象と augmentation を保持する。準同型判定は OrdinaryPullbackQuasiIso で接続する。
使われ方：G-1 f の通常 pullback 比較と同じ部分圏を零化する平坦 Verdier 商に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
def dgGluingPullbackProperty (X : DGGluingObject R C D M) : Prop :=
  IsEquivalencePathVertex ((dgGluingUniverseDerivedAugmentationArrowFamily R C D M).app
    (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
abbrev DGGluingPullbackObject :=
  DGFullSubcategory (DGGluingObject R C D M) (dgGluingPullbackProperty R C D M)
def dgGluingPullbackInclusion :
    DGFunctor R (DGGluingPullbackObject R C D M) (DGGluingObject R C D M) :=
  dgFullSubcategoryInclusion R _ _
lemma dgGluingPullbackProperty_iff_laxVertex (X : DGGluingObject R C D M) :
    dgGluingPullbackProperty R C D M X ↔
      F2.IsLaxEquivalenceVertex (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)
        ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (Simplex.vertex X))) := by
  change _ ↔ IsEquivalencePathVertex
    ((dgGluingUniverseDerivedNerveLaxComparison R C D M ≫ F2.laxPullbackArrow
      (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)))
  rw [dgGluingUniverseDerivedNerveLaxComparison_arrow]
  rfl
lemma dgGluingPullbackInclusion_hom (X Y : DGGluingPullbackObject R C D M) :
    (dgGluingPullbackInclusion R C D M).map X Y =
      𝟙 (homObject R (DGGluingObject R C D M) X.val Y.val) := rfl
instance dgGluingPullbackObject_small [Small.{u} D] :
    Small.{u} (DGGluingPullbackObject R C D M) := inferInstance
end SerrePositivity.InfinityCategories
