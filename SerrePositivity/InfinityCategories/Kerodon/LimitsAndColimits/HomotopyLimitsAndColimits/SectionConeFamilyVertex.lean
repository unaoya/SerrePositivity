module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：切断の全族から錐への既存の写像の零次成分を、元のcoslice切断の錐と照合する。
方針：既存の右直積比較のパラメーター自然性と、零単体での単位則を使う。
規約：HTT §1.2.13、Kerodon Example 4.6.6.8（Tag 04J5）の既存構成の法則。
使われ方：R04-RI。相対同型の像を元の指定極限錐の頂点へ戻す証明分割。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 元の切断の指定頂点で、全族の錐への比較は同じuncurryの錐を回収する。 -/
@[cite HTT "1.2.13" (partial := special) "既存の切断から錐への全族の零次成分の計算法則。"]
lemma sectionConeFamilyMap_section_vertex {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) (s : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (hs : s ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) = p) :
    (sectionConeFamilyMap p x).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p s hs) =
    coneFamilyVertexEquiv p (cosliceSectionCone s hs) := by
  let T := coherentConeSectionSpace p x
  let v : (Δ[0] : SSet.{u}) ⟶ T := SSet.yonedaEquiv.symm
    (relativeFunctorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p s hs)
  have hv : relativeFunctorUncurry v = fst K (Δ[0] : SSet.{u}) ≫ s := by
    dsimp only [v, T, coherentConeSectionSpace]
    unfold relativeFunctorUncurry
    rw [SSet.yonedaEquiv_symm_comp]
    change uncurry (SSet.yonedaEquiv.symm (functorVertex s)) = _
    exact uncurry_yoneda_functorVertex s
  have hn := relativeFunctorUncurry_naturality (𝟙 T) v
  rw [Category.comp_id] at hn
  have he : (join (Δ[0] : SSet.{u}) K ◁ v) ≫ sectionConeFamilyUncurry p x =
      fst (join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ sliceUnderUncurry s := by
    unfold sectionConeFamilyUncurry
    rw [← Category.assoc, joinTensorRight_parameter, Category.assoc,
      ← sliceUnderUncurry_precomp, ← hn, hv, sliceUnderUncurry_precomp,
      ← Category.assoc, joinTensorRight_unit]
  apply Subtype.ext
  change (curry (sectionConeFamilyUncurry p x)).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p s hs) =
      functorVertex (sliceUnderUncurry s)
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, he, uncurry_yoneda_functorVertex]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
