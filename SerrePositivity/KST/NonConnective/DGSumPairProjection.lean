module

public import SerrePositivity.KST.NonConnective.DGSumFamilyInclusion
public import SerrePositivity.KST.NonConnective.DGClosedHomLinearity

/-!
概要：実二項 dg 関手直和の、同じ閉射影と全 Hom 自然性。
方針：両注入に制限し、恒等射・零射の前後合成を全複体で計算する。
規約：実直和の選択を保持する。使われ方：dg swindle の分裂 cofiber 族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {C : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (F : WalkingPair → _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D))

/-- 指定した二項実直和から同じ指定成分への元の射影。 -/
def dgSumPairProjection : (j : WalkingPair) → (X : C) →
    dgSumFamilyObj R D F X ⟶ (F j).obj X
  | .left, _ => Sigma.desc (fun k ↦ by
      cases k
      · exact 𝟙 _
      · exact 0)
  | .right, _ => Sigma.desc (fun k ↦ by
      cases k
      · exact 0
      · exact 𝟙 _)

/-- 指定射影は元の両 dg 関手の全斉次作用と可換。 -/
lemma dgSumPairProjection_naturality (j : WalkingPair) (X Y : C) :
    dgSumFamilyHom R D F X Y ≫ eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgSumFamilyObj R D F X) (dgSumPairProjection R D F j Y) =
    (F j).map X Y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgSumPairProjection R D F j X) ((F j).obj Y) := by
  apply (_root_.SerrePositivity.DifferentialGraded.moduleCoproductHomIsLimit R D (fun k ↦ (F k).obj X) ((F j).obj Y)).hom_ext
  intro k
  change (dgSumFamilyHom R D F X Y ≫ eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) _
    (dgSumPairProjection R D F j Y)) ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι (fun k ↦ (F k).obj X) k.as) _ =
    ((F j).map X Y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgSumPairProjection R D F j X) _) ≫
        eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (Sigma.ι (fun k ↦ (F k).obj X) k.as) _
  rw [Category.assoc, eHom_whisker_exchange, ← Category.assoc,
    dgSumFamilyHom_injection, Category.assoc, ← eHomWhiskerLeft_comp,
    Category.assoc, ← eHomWhiskerRight_comp]
  rcases k with ⟨k⟩
  cases j <;> cases k <;>
    simp only [dgSumPairProjection, Sigma.ι_comp_desc,
      eHomWhiskerLeft_id, eHomWhiskerRight_id, dgClosedHomPost_zero,
      dgClosedHomPre_zero, Category.comp_id, comp_zero]

/-- 同じ指定射影は全斉次射に自然な厳密 dg 自然変換。 -/
def dgSumPairStrictProjection (j : WalkingPair) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgSumFamilyFunctor R D F) (F j) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransOfUnitNaturality
    (F := dgSumFamilyFunctor R D F) (G := F j)
    (fun X ↦ eHomEquiv (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgSumPairProjection R D F j X)) (by
      intro X Y
      simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
        dgSumFamilyFunctor, _root_.SerrePositivity.DifferentialGraded.homObject] using
        dgSumPairProjection_naturality R D F j X Y)

end SerrePositivity.KST.NonConnective
