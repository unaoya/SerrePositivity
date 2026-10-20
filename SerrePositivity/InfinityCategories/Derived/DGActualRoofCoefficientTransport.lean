module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofClosedCoefficients
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofHomInclusion

/-! # 回収した閉係数と元の相対輸送の同定

概要：回収した同じ閉分母上の係数の実屋根像を、共通 fiber 還元の始端に厳密に同定する。
方針：頂点の等式による Hom 輸送と既存の fiber 同型の両逆関係を使う。
規約：任意の還元データに適用。使われ方：追加分母後の充填と元の相対問題の輸送の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D)

omit [Small.{u} D] in
/-- 頂点等式による元係数の逆輸送は、同じ実屋根包含に一致する。 -/
lemma dgRoofHomInclusion_vertex_transport
    {σ τ : (dgVerdierOver A D P x : SSet) _⦋0⦌} (h : σ = τ) :
    (eqToIso (congrArg (fun z : (dgVerdierOver A D P x : SSet) _⦋0⦌ => DGNerve.pinchedHom A D
      (dgOverVertexSource A D x z.val) y) h)).inv ≫ dgRoofHomInclusion A D P x y σ =
      dgRoofHomInclusion A D P x y τ := by
  cases h
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]

/-- 頂点等式による商係数の逆輸送も、同じ実商屋根包含に一致する。 -/
lemma dgQuotientRoofHomInclusion_vertex_transport
    {σ τ : (dgVerdierOver A D P x : SSet) _⦋0⦌} (h : σ = τ) :
    (eqToIso (congrArg (fun z : (dgVerdierOver A D P x : SSet) _⦋0⦌ =>
      DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x z.val))
      ((DGQuotient.inclusion A D P).obj y)) h)).inv ≫ dgQuotientRoofHomInclusion A D P x y σ =
      dgQuotientRoofHomInclusion A D P x y τ := by
  cases h
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]

variable {L K : SSet.{max u v}} {i : L ⟶ K}
variable {a : L ⟶ dgRoofCorrespondence A D P x y}
variable {g : K ⟶ dgQuotientRoofCorrespondence A D P x y}
variable (R : DGActualRoofFiberReduction A D P x y i a g)

/-- 回収した同じ閉分母上の元 Hom 包含は元の共通頂点の包含。 -/
lemma dgActualRoofReductionDenominator_inclusion :
    dgClosedRoofHomInclusion A D P x y (dgActualRoofReductionDenominator A D P x y R) =
      dgRoofHomInclusion A D P x y R.cone.vertex :=
  dgRoofHomInclusion_vertex_transport A D P x y
    (dgActualRoofReductionDenominator_vertex A D P x y R)

/-- 回収した同じ閉分母上の商 Hom 包含も元の共通頂点の包含。 -/
lemma dgActualRoofReductionDenominator_quotientInclusion :
    dgQuotientClosedRoofHomInclusion A D P x y (dgActualRoofReductionDenominator A D P x y R) =
      dgQuotientRoofHomInclusion A D P x y R.cone.vertex :=
  dgQuotientRoofHomInclusion_vertex_transport A D P x y
    (dgActualRoofReductionDenominator_vertex A D P x y R)

/-- 閉表示した元係数の実屋根像は同じ還元境界の fiber 包含。 -/
lemma dgActualRoofClosedSourceCoefficient_inclusion :
    dgActualRoofClosedSourceCoefficient A D P x y R ≫
      dgClosedRoofHomInclusion A D P x y (dgActualRoofReductionDenominator A D P x y R) =
      R.boundary ≫ vertexFiberι (dgRoofCorrespondenceProjection A D P x y) R.cone.vertex := by
  rw [dgActualRoofReductionDenominator_inclusion]
  change (R.boundary ≫ (dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫
    ((dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

/-- 閉表示した商係数の実屋根像も同じ還元全体の fiber 包含。 -/
lemma dgActualRoofClosedTargetCoefficient_inclusion :
    dgActualRoofClosedTargetCoefficient A D P x y R ≫
      dgQuotientClosedRoofHomInclusion A D P x y (dgActualRoofReductionDenominator A D P x y R) =
      R.target ≫ vertexFiberι (dgQuotientRoofCorrespondenceProjection A D P x y) R.cone.vertex := by
  rw [dgActualRoofReductionDenominator_quotientInclusion]
  change (R.target ≫ (dgQuotientRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫
    ((dgQuotientRoofCorrespondenceFiberIso A D P x y R.cone.vertex).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories
