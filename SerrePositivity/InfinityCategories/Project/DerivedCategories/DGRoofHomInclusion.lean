module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofFiberComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictRoofQuotientVertex

/-! # 任意の実分母上の Hom の実屋根への包含

概要：任意の実分母の始域からの pinched Hom を実屋根の全空間に含める。
方針：実 fiber 同型の逆と fiber 包含を合成し、二射影と商比較を照合する。
規約：恒等分母に制限しない。使われ方：指定分母上の有限ホモトピーの実屋根化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 任意の実分母の始域からの Hom を、その分母上の元の実屋根へ含める。 -/
def dgRoofHomInclusion (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val) y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) σ

/-- 元の Hom 包含の分母射影は、指定した実分母に定値。 -/
lemma dgRoofHomInclusion_projection (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      SSet.const σ := by
  rw [dgRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 元の Hom 包含の分子成分は、実 pinched Hom の標準 slice 表示。 -/
lemma dgRoofHomInclusion_target (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).hom).mp
  simpa only [dgRoofHomInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceTarget, Category.assoc, Iso.hom_inv_id_assoc]
    using (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso_hom_target A D P x y σ).symm

variable [Small.{u} D]

/-- 任意の元の実分母の始域の商 Hom を、その分母上の実商屋根へ含める。 -/
def dgQuotientRoofHomInclusion (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val))
      ((DGQuotient.inclusion A D P).obj y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) σ

/-- 商 Hom 包含の分母射影も、元の指定実分母に定値。 -/
lemma dgQuotientRoofHomInclusion_projection (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgQuotientRoofHomInclusion A D P x y σ ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y = SSet.const σ := by
  rw [dgQuotientRoofHomInclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 商 Hom 包含の分子成分も、実商 pinched Hom の標準 slice 表示。 -/
lemma dgQuotientRoofHomInclusion_target (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgQuotientRoofHomInclusion A D P x y σ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget A D P x y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val))) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom).mp
  simpa only [dgQuotientRoofHomInclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceTarget,
    Category.assoc, Iso.hom_inv_id_assoc]
    using (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso_hom_target A D P x y σ).symm

/-- 任意の実分母上の Hom 包含は、元の商 Hom 鎖写像と厳密に可換。 -/
lemma dgRoofHomInclusion_comparison (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val) y) ≫ dgQuotientRoofHomInclusion A D P x y σ := by
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ
  have h : i.inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap A D P x y σ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val) y) ≫ j.inv := by
    apply (cancel_mono j.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap_conjugate A D P x y σ
  dsimp only [dgRoofHomInclusion, dgQuotientRoofHomInclusion]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberMap_ι, ← Category.assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
