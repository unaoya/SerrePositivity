module
public import SerrePositivity.InfinityCategories.Derived.DGRoofFiberComparison
public import SerrePositivity.InfinityCategories.Derived.DGStrictRoofQuotientVertex

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 任意の実分母の始域からの Hom を、その分母上の元の実屋根へ含める。 -/
def dgRoofHomInclusion (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    DGNerve.pinchedHom A D (dgOverVertexSource A D x σ.val) y ⟶
      dgRoofCorrespondence A D P x y :=
  (dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
    vertexFiberι (dgRoofCorrespondenceProjection A D P x y) σ

/-- 元の Hom 包含の分母射影は、指定した実分母に定値。 -/
lemma dgRoofHomInclusion_projection (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ dgRoofCorrespondenceProjection A D P x y =
      SSet.const σ := by
  rw [dgRoofHomInclusion, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 元の Hom 包含の分子成分は、実 pinched Hom の標準 slice 表示。 -/
lemma dgRoofHomInclusion_target (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ dgRoofCorrespondenceTarget A D P x y =
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex (dgOverVertexSource A D x σ.val)) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex (dgOverVertexSource A D x σ.val)) := by
  apply (cancel_epi (dgRoofCorrespondenceFiberIso A D P x y σ).hom).mp
  simpa only [dgRoofHomInclusion, dgRoofCorrespondenceTarget, Category.assoc, Iso.hom_inv_id_assoc]
    using (dgRoofCorrespondenceFiberIso_hom_target A D P x y σ).symm

variable [Small.{u} D]

/-- 任意の元の実分母の始域の商 Hom を、その分母上の実商屋根へ含める。 -/
def dgQuotientRoofHomInclusion (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val))
      ((DGQuotient.inclusion A D P).obj y) ⟶ dgQuotientRoofCorrespondence A D P x y :=
  (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).inv ≫
    vertexFiberι (dgQuotientRoofCorrespondenceProjection A D P x y) σ

/-- 商 Hom 包含の分母射影も、元の指定実分母に定値。 -/
lemma dgQuotientRoofHomInclusion_projection (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgQuotientRoofHomInclusion A D P x y σ ≫
      dgQuotientRoofCorrespondenceProjection A D P x y = SSet.const σ := by
  rw [dgQuotientRoofHomInclusion, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 商 Hom 包含の分子成分も、実商 pinched Hom の標準 slice 表示。 -/
lemma dgQuotientRoofHomInclusion_target (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgQuotientRoofHomInclusion A D P x y σ ≫ dgQuotientRoofCorrespondenceTarget A D P x y =
      (pinchedHomSliceFiberIso (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val)))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
          (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val))) := by
  apply (cancel_epi (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom).mp
  simpa only [dgQuotientRoofHomInclusion, dgQuotientRoofCorrespondenceTarget,
    Category.assoc, Iso.hom_inv_id_assoc]
    using (dgQuotientRoofCorrespondenceFiberIso_hom_target A D P x y σ).symm

/-- 任意の実分母上の Hom 包含は、元の商 Hom 鎖写像と厳密に可換。 -/
lemma dgRoofHomInclusion_comparison (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofHomInclusion A D P x y σ ≫ dgRoofCorrespondenceMap A D P x y =
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (dgOverVertexSource A D x σ.val) y) ≫ dgQuotientRoofHomInclusion A D P x y σ := by
  let i := dgRoofCorrespondenceFiberIso A D P x y σ
  let j := dgQuotientRoofCorrespondenceFiberIso A D P x y σ
  have h : i.inv ≫ dgRoofCorrespondenceFiberMap A D P x y σ =
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (dgOverVertexSource A D x σ.val) y) ≫ j.inv := by
    apply (cancel_mono j.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact dgRoofCorrespondenceFiberMap_conjugate A D P x y σ
  dsimp only [dgRoofHomInclusion, dgQuotientRoofHomInclusion]
  rw [Category.assoc, ← dgRoofCorrespondenceFiberMap_ι, ← Category.assoc, h, Category.assoc]

end SerrePositivity.InfinityCategories
