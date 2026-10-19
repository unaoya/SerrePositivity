module
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondenceFiber

/-! # 実屋根の右ファイブレーション間の商比較

概要：実 Verdier over ∞ 圏を固定して、元の屋根の全空間を商側の全空間へ写す。
方針：標的 y の slice を商へ後合成し、指定終点の等式で輸送して pullback へ持ち上げる。
規約：平坦性・前三角性は不要。使われ方：実高次屋根による写像空間の局所化比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の指定頂点の点図式を商へ送ると、同じ対象の商像の点図式。 -/
lemma dgQuotientNervePoint (P : Set D) (y : D) :
    (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y) ≫
      dgQuotientNerveProjection A D P =
    (SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj y)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)).injective
  rfl

/-- y へ入る実 slice を、指定された商像へ入る実 slice へ写す。 -/
def dgQuotientTargetSliceMap (P : Set D) (y : D) :
    sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))) :=
  sliceOverPostcomp _ (dgQuotientNerveProjection A D P) ≫
    (eqToIso (congrArg sliceOver (dgQuotientNervePoint A D P y))).hom

/-- 標的 slice の商比較は、元の始域の商像への射影を厳密に回収する。 -/
lemma dgQuotientTargetSliceMap_projection (P : Set D) (y : D) :
    dgQuotientTargetSliceMap A D P y ≫ sliceOverProjection _ =
      sliceOverProjection _ ≫ dgQuotientNerveProjection A D P := by
  dsimp only [dgQuotientTargetSliceMap]
  rw [Category.assoc, F1B.kanSliceOverProjection_eqTransport,
    F1B.kanSliceOverPostcomp_projection]
  exact dgQuotientNervePoint A D P y

/-- 元の実屋根の右ファイブレーションから商側の実屋根への、全高次単体を保つ比較。 -/
def dgRoofCorrespondenceMap (P : Set D) (x y : D) :
    dgRoofCorrespondence A D P x y ⟶ dgQuotientRoofCorrespondence A D P x y :=
  pullback.lift (pullback.fst _ _ ≫ dgQuotientTargetSliceMap A D P y)
    (dgRoofCorrespondenceProjection A D P x y) (by
      rw [Category.assoc, dgQuotientTargetSliceMap_projection, ← Category.assoc,
        pullback.condition, Category.assoc]
      rfl)

/-- 実屋根の比較は、元の実分母 over 圏への射影を厳密に保つ。 -/
lemma dgRoofCorrespondenceMap_projection (P : Set D) (x y : D) :
    dgRoofCorrespondenceMap A D P x y ≫ dgQuotientRoofCorrespondenceProjection A D P x y =
      dgRoofCorrespondenceProjection A D P x y :=
  pullback.lift_snd _ _ _

/-- 実屋根の比較の実射側成分は、元の標的 slice の商写像。 -/
lemma dgRoofCorrespondenceMap_target (P : Set D) (x y : D) :
    dgRoofCorrespondenceMap A D P x y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ dgQuotientTargetSliceMap A D P y :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories
