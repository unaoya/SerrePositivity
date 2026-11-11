module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeBFComparison

/-! # 元の直通列点での BF 比較の両端の厳密な回収
概要：全精密化族の BF 比較の直通列境界を、既存の同じ BF 境界とその実合成へ照合する。
方針：元の三つの射影と同じ BF 族の境界の式を、全写像空間の実射に適用する。
規約：成分や π 群でなく、元の BF 写像空間への射そのものの等号を証明する。
使われ方：入力二射の合成面を、元の同じ境界の実比較として使う。
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

/-- 共通直通列点の二入力への射影は、同じ二つの元の直通列点の射対。 -/
lemma compositionStringPair_direct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ compositionStringPair f g =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, compositionStringPair_first, lift_fst, compositionStringFirst_direct]
  · rw [Category.assoc, compositionStringPair_second, lift_snd, compositionStringSecond_direct]

/-- 直接厳密化側の直通列境界は、合成射の既存の同じ BF 境界。 -/
lemma monicKPrismNativeDirectBFFamily_boundary :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ monicKPrismNativeDirectBFFamily F f g =
      monicKPrismTracedBFBoundary F (f ≫ g) := by
  rw [monicKPrismNativeDirectBFFamily, ← Category.assoc,
    compositionStringComposite_direct, monicKPrismTracedBFFamily_boundary]

/-- 合成側の直通列境界は、元の二つの既存 BF 境界を同じ写像空間で実合成した射。 -/
lemma monicKPrismNativeCompositeBFFamily_boundary :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ≫ monicKPrismNativeCompositeBFFamily F f g =
      lift (monicKPrismTracedBFBoundary F f) (monicKPrismTracedBFBoundary F g) ≫
        OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj x))
          (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z)) := by
  rw [monicKPrismNativeCompositeBFFamily, ← Category.assoc, compositionStringPair_direct]
  rw [monicKPrismTracedCompositionFamily, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
      monicKPrismTracedBFFamily_boundary]

/-- 元の合成射の BF 境界から、元の二つの BF 境界の実合成への実比較円柱。 -/
def monicKPrismTracedBFCompositionBoundary : SSet.Homotopy
    (monicKPrismTracedBFBoundary F (f ≫ g))
    (lift (monicKPrismTracedBFBoundary F f) (monicKPrismTracedBFBoundary F g) ≫
      OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj x))
        (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z))) :=
  familyHomotopyEndpointTransport (monicKPrismNativeBFComparisonBoundaryData F f g).val
    (monicKPrismNativeDirectBFFamily_boundary F f g).symm
    (monicKPrismNativeCompositeBFFamily_boundary F f g)

/-- 両端の表示を移しても、先に選んだ同じ境界円柱全体を保持する。 -/
lemma monicKPrismTracedBFCompositionBoundary_h :
    (monicKPrismTracedBFCompositionBoundary F f g).h =
      (monicKPrismNativeBFComparisonBoundaryData F f g).val.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 全精密化 BF 比較の直通列境界は、既存の二境界の同じ実合成比較円柱。 -/
lemma monicKPrismNativeBFComparisonData_composition_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeBFComparisonData F f g).val.h =
      (monicKPrismTracedBFCompositionBoundary F f g).h :=
  (monicKPrismNativeBFComparisonData_boundary F f g).trans
    (monicKPrismTracedBFCompositionBoundary_h F f g).symm

end SerrePositivity.KST.SConstruction
