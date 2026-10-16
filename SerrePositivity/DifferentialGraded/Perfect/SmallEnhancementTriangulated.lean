module
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated

/-! # 小さいperfect dg代表系のH⁰三角構造

小さい代表系ではshift後の加群を選択した代表へ戻す。
全Homを保つdg包含との比較は別に整合性を与える。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 小さい射影的perfect dg代表系の実際のH⁰。 -/
abbrev SmallPerfectDGHomotopyCategoryOver (S : Set D) :=
  HomotopyCategory A (SmallPerfectDGModuleOver A D S)

/-- 主Perfでshiftした後、選択した小さい射影的代表へ戻るH⁰関手。 -/
def smallPerfectDGShiftHomotopyFunctor (S : Set D) (s : ℤ) :
    SmallPerfectDGHomotopyCategoryOver A D S ⥤ SmallPerfectDGHomotopyCategoryOver A D S :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).functor ⋙
    shiftFunctor (PerfectModuleCategoryOver A D S) s ⋙
      (smallPerfectDGModuleHomotopyEquivalence A D S).inverse

/-- 代表を取り直したshiftの主Perf比較は、同値の余単位から構成する。 -/
def smallPerfectDGShiftHomotopyIso (S : Set D) (s : ℤ) :
    smallPerfectDGShiftHomotopyFunctor A D S s ⋙
      (smallPerfectDGModuleHomotopyEquivalence A D S).functor ≅
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor ⋙
      shiftFunctor (PerfectModuleCategoryOver A D S) s := by
  let e := smallPerfectDGModuleHomotopyEquivalence A D S
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.functor
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (shiftFunctor (PerfectModuleCategoryOver A D S) s) e.counitIso ≪≫
      (shiftFunctor (PerfectModuleCategoryOver A D S) s).rightUnitor)

/-- 小さいH⁰のshiftにzero/add coherenceを誘導し、対象の代表選択を整合させる。 -/
instance smallPerfectDGHomotopyHasShift (S : Set D) :
    HasShift (SmallPerfectDGHomotopyCategoryOver A D S) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor).hasShift
      (smallPerfectDGShiftHomotopyFunctor A D S) (smallPerfectDGShiftHomotopyIso A D S)

/-- 誘導した各shift関手は、定義した代表取り直し関手そのものである。 -/
lemma smallPerfectDGHomotopy_shiftFunctor (S : Set D) (s : ℤ) :
    shiftFunctor (SmallPerfectDGHomotopyCategoryOver A D S) s =
      smallPerfectDGShiftHomotopyFunctor A D S s := rfl

/-- 小さい代表系の各整数shiftは加法的である。 -/
instance smallPerfectDGHomotopyShiftAdditive (S : Set D) (s : ℤ) :
    (shiftFunctor (SmallPerfectDGHomotopyCategoryOver A D S) s).Additive := by
  rw [smallPerfectDGHomotopy_shiftFunctor]
  dsimp [smallPerfectDGShiftHomotopyFunctor]
  infer_instance

/-- 小さいH⁰と主Perfの同値の順関手は誘導shiftと整合する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceFunctorCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).functor.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (smallPerfectDGModuleHomotopyEquivalence A D S).functor)
    (smallPerfectDGShiftHomotopyFunctor A D S) (smallPerfectDGShiftHomotopyIso A D S)

/-- 小さいH⁰同値の逆関手のshift比較を、順関手の比較から随伴で構成する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceInverseCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).inverse.CommShift ℤ :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).commShiftInverse ℤ

/-- 小さいH⁰同値の単位・余単位もshiftに整合する。 -/
instance smallPerfectDGModuleHomotopyEquivalenceCommShift (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).CommShift ℤ :=
  (smallPerfectDGModuleHomotopyEquivalence A D S).commShift_of_functor ℤ

/-- 元の小さい代表比較に同じ整合的shift比較を公開する。 -/
instance smallPerfectDGModuleToPerfectCommShift (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).CommShift ℤ :=
  smallPerfectDGModuleHomotopyEquivalenceFunctorCommShift A D S

/-- 主Perfの零対象を選択した小さい代表へ戻す。 -/
instance smallPerfectDGHomotopyHasZeroObject (S : Set D) :
    HasZeroObject (SmallPerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonHasZeroObject (smallPerfectDGModuleHomotopyEquivalence A D S)

/-- 誘導shiftの下で主Perfのdistinguished三角形を引き戻す。 -/
instance smallPerfectDGHomotopyPretriangulated (S : Set D) :
    Pretriangulated (SmallPerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonPretriangulated (smallPerfectDGModuleHomotopyEquivalence A D S)

/-- 小さいH⁰比較は、定義した三角構造について三角関手となる。 -/
instance smallPerfectDGModuleToPerfectIsTriangulated (S : Set D) :
    (smallPerfectDGModuleToPerfect A D S).IsTriangulated where
  map_distinguished _ hT := hT

/-- 小さいH⁰の八面体公理は、主Perfへの完全忠実比較で反映する。 -/
instance smallPerfectDGHomotopyIsTriangulated (S : Set D) :
    IsTriangulated (SmallPerfectDGHomotopyCategoryOver A D S) :=
  IsTriangulated.of_fully_faithful_triangulated_functor (smallPerfectDGModuleToPerfect A D S)

/-- 小さいdg代表系のH⁰と主Perfの同値は、shift整合的な三角同値である。 -/
instance smallPerfectDGModuleHomotopyEquivalenceIsTriangulated (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (smallPerfectDGModuleToPerfect A D S).IsTriangulated
    infer_instance)

/-- 小さい代表のH⁰包含と全射影的比較の合成は、元の小さいPerf比較そのものである。 -/
def smallPerfectDGModuleInclusionPerfectIso (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy ⋙ perfectDGModuleToPerfect A D S ≅
      smallPerfectDGModuleToPerfect A D S := Iso.refl _

/-- 小さい代表の実際のdg包含は、H⁰で双方の整数shiftと整合する。 -/
instance smallPerfectDGModuleInclusionHomotopyCommShift (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (smallPerfectDGModuleInclusionPerfectIso A D S) ℤ

/-- 小さい比較の因子化の自然同型もzero/add coherenceを保つ。 -/
instance smallPerfectDGModuleInclusionPerfectIsoCommShift (S : Set D) :
    NatTrans.CommShift (smallPerfectDGModuleInclusionPerfectIso A D S).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (smallPerfectDGModuleInclusionPerfectIso A D S) ℤ

/-- 小さい代表系のH⁰包含は三角関手。主Perfへの完全忠実比較で判定する。 -/
instance smallPerfectDGModuleInclusionHomotopyIsTriangulated (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (smallPerfectDGModuleInclusionPerfectIso A D S)).mpr inferInstance

/-- 小さい代表系のH⁰包含は、既に証明した完全忠実性と本質的全射性により同値である。 -/
instance smallPerfectDGModuleInclusionHomotopyIsEquivalence (S : Set D) :
    (smallPerfectDGModuleInclusion A D S).onHomotopy.IsEquivalence where

end SerrePositivity.DifferentialGraded
