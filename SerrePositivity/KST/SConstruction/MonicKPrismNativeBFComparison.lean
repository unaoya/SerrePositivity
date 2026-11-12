module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeRawComparison
public import SerrePositivity.KST.SConstruction.PrescribedRawHomotopyLift

/-! # 元の全 raw 比較を保つ指定境界付き BF 合成比較
概要：直接厳密化と BF 合成の二族を、先に選んだ直通列境界と全 raw 円柱を保って比較する。
方針：直通列点上の BF 比較を先に持ち上げ、同じ境界と全射影を保つ相対延長を行う。
規約：元の全段 raw 円柱・先に指定した境界円柱・二つの BF 族の全体を厳密に回収する。
使われ方：入力の合成面と高次の指定境界を持つ coherent な K 関手化への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 共通三精密化上の元の合成射の直接 BF 厳密化。 -/
def monicKPrismNativeDirectBFFamily :=
  nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedBFFamily F (f ≫ g)

/-- 共通三精密化上の元の二つの BF 族の実合成。 -/
def monicKPrismNativeCompositeBFFamily :=
  compositionStringPair f g ≫ monicKPrismTracedCompositionFamily F f g

/-- 直接 BF 族の実射影は同じ元の直接厳密化 raw 族。 -/
lemma monicKPrismNativeDirectBFFamily_projection :
    monicKPrismNativeDirectBFFamily F f g ≫ kRawMappingProjection (F.obj x) (F.obj z) =
      nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) := by
  rw [monicKPrismNativeDirectBFFamily, Category.assoc, monicKPrismTracedBFFamily_projection]

/-- 合成 BF 族の実射影も同じ元の raw 合成族。 -/
lemma monicKPrismNativeCompositeBFFamily_projection :
    monicKPrismNativeCompositeBFFamily F f g ≫ kRawMappingProjection (F.obj x) (F.obj z) =
      compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g := by
  rw [monicKPrismNativeCompositeBFFamily, Category.assoc,
    monicKPrismTracedCompositionFamily_projection]

/-- 元の全段 raw 比較を、同じ BF 族の実射影の間に表示する。 -/
def monicKPrismNativeProjectedRawComparison : SSet.Homotopy
    (monicKPrismNativeDirectBFFamily F f g ≫ kRawMappingProjection (F.obj x) (F.obj z))
    (monicKPrismNativeCompositeBFFamily F f g ≫ kRawMappingProjection (F.obj x) (F.obj z)) :=
  familyHomotopyEndpointTransport (monicKPrismNativeRawComparison F f g)
    (monicKPrismNativeDirectBFFamily_projection F f g)
    (monicKPrismNativeCompositeBFFamily_projection F f g).symm

/-- 実射影の表示へ移しても元の全 raw 円柱そのものを保つ。 -/
lemma monicKPrismNativeProjectedRawComparison_h :
    (monicKPrismNativeProjectedRawComparison F f g).h =
      (monicKPrismNativeRawComparison F f g).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 直通列点上で先に選ぶ、元の全 raw 比較を持ち上げた BF 境界円柱。 -/
def monicKPrismNativeBFComparisonBoundaryData :=
  rawHomotopyLiftData (kRawMappingProjection (F.obj x) (F.obj z))
    (kRawMappingProjection_rlp (F.obj x) (F.obj z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ monicKPrismNativeDirectBFFamily F f g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ monicKPrismNativeCompositeBFFamily F f g)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (monicKPrismNativeProjectedRawComparison F f g)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)))

/-- 先に選んだ同じ BF 境界と元の全 raw 円柱を保持する全精密化族の実比較。 -/
def monicKPrismNativeBFComparisonData :=
  prescribedRawHomotopyLiftData (kRawMappingProjection (F.obj x) (F.obj z))
    (kRawMappingProjection_rlp (F.obj x) (F.obj z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
    (monicKPrismNativeDirectBFFamily F f g) (monicKPrismNativeCompositeBFFamily F f g)
    (monicKPrismNativeProjectedRawComparison F f g)
    (monicKPrismNativeBFComparisonBoundaryData F f g).val
    (monicKPrismNativeBFComparisonBoundaryData F f g).property

/-- 全 BF 比較の実射影は、累積補正で構成した元の全段 raw 円柱そのもの。 -/
lemma monicKPrismNativeBFComparisonData_projection :
    (monicKPrismNativeBFComparisonData F f g).val.h ≫
        kRawMappingProjection (F.obj x) (F.obj z) =
      (monicKPrismNativeRawComparison F f g).h :=
  (monicKPrismNativeBFComparisonData F f g).property.1.trans
    (monicKPrismNativeProjectedRawComparison_h F f g)

/-- 全精密化族の実比較は、先に選んだ同じ BF 境界円柱の全時刻を回収する。 -/
lemma monicKPrismNativeBFComparisonData_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeBFComparisonData F f g).val.h =
      (monicKPrismNativeBFComparisonBoundaryData F f g).val.h :=
  (monicKPrismNativeBFComparisonData F f g).property.2

end SerrePositivity.KST.SConstruction
