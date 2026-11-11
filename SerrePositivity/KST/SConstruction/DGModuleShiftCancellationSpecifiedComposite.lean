module
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationSpecified

/-!
概要：同じ指定相殺同型を閉成分に持つ全厳密合成を作る。
方針：先に次数を輸送した加法逆比較と零 shift 比較を合成する。
規約：元の指定相殺同型を保持する。
使われ方：実逆回転全比較の相殺因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma compositeRecovery {P : Type (max (u + 1) v)} [DGCategory R P]
    (F G H : DGFunctor R P (RightModule R D))
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) (x : P)
    (a : ForgetEnrichment.of (Complex R) (F.obj x) ⟶ ForgetEnrichment.of (Complex R) (G.obj x))
    (b : ForgetEnrichment.of (Complex R) (G.obj x) ⟶ ForgetEnrichment.of (Complex R) (H.obj x))
    (ha : dgModuleNaturalConeArrow R D F G η x = a)
    (hb : dgModuleNaturalConeArrow R D G H θ x = b) :
    dgModuleNaturalConeArrow R D F H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ) x = a ≫ b :=
  (dgModuleNaturalConeArrow_comp R D F G H η θ x).trans
    (congrArg₂ (fun f g => f ≫ g) ha hb)

/-- 概要：元二重 shift の同じ指定実相殺同型。
方針：先に次数を輸送した元加法同型と元零 shift 同型を合成。
規約：元成分を保持。使われ方：全相殺比較の指定成分。 -/
def dgModuleSpecifiedCancellationIso (M : RightModule R D) :
    ForgetEnrichment.of (Complex R) (shiftModule (-1) (shiftModule 1 M)) ≅
      ForgetEnrichment.of (Complex R) M :=
  (dgModuleShiftAddSpecifiedIso R D M).symm ≪≫ moduleShiftZeroIsoObj R D M

/-- 概要：同じ指定実相殺を持つ全厳密比較。
方針：同じ二因子を全厳密合成する。
規約：元相殺成分を保持。使われ方：実逆回転全比較の終辺。 -/
def dgModuleSpecifiedCancellationStrictComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1)))
      (DGFunctor.id (RightModule R D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleShiftAddInvSpecifiedComparison R D)
    (dgModuleShiftZeroStrictComparison R D)

/-- 概要：元指定相殺全比較の閉射は同じ元実相殺同型。
方針：全厳密合成の回収を次数零で先に抽象化する。
規約：元二因子の指定閉射を保持。使われ方：全実逆回転比較の成分回収。 -/
lemma dgModuleSpecifiedCancellationStrictComparison_arrow (M : RightModule R D) :
    dgModuleNaturalConeArrow R D
      ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1)))
      (DGFunctor.id (RightModule R D)) (dgModuleSpecifiedCancellationStrictComparison R D) M =
      (dgModuleSpecifiedCancellationIso R D M).hom :=
  compositeRecovery R D _ (moduleShiftDG R D 0) _
    (dgModuleShiftAddInvSpecifiedComparison R D) (dgModuleShiftZeroStrictComparison R D) M
    (dgModuleShiftAddSpecifiedIso R D M).inv (moduleShiftZeroIsoObj R D M).hom
    (dgModuleShiftAddInvSpecifiedComparison_arrow R D M)
    (dgModuleShiftZeroStrictComparison_arrow R D M)

/-- 概要：指定相殺は従来の実逆回転終域同型そのもの。
方針：整数和の reflexive 輸送を簡約する。
規約：旧公開同型不変。使われ方：元実逆回転成分との厳密照合。 -/
lemma dgModuleSpecifiedCancellationIso_eq (M : RightModule R D) :
    dgModuleSpecifiedCancellationIso R D M =
      dgModuleInverseRotationTargetIso R D (N := ForgetEnrichment.of (Complex R) M) := rfl
end SerrePositivity.KST.SConstruction
