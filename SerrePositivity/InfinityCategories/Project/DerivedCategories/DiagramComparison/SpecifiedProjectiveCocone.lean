module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceColimitCones
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentCoconeTransport
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction

/-!
# 計算済みの指定余錐を射影的模型へ持ち上げる

## 概要
同じ頂点と全単体を持つ余錐を充満部分圏へ戻し、既存D(A)へ移す。
## 方針
射影性はH⁰での実retractから戻し、余極限性は充満包含で反映する。
## 規約
実現の頂点を別のbarへ取り替えない。
## 使われ方
HA 1.2.4、HTT 4.2.4.1。strict実現の計算済み余錐の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- H⁰での同じ可逆射は、標的の射影性を戻す。 -/
theorem moduleProjective_of_isIso_onHomotopy {M N : ModuleCategory R D} (f : M ⟶ N)
    (hf : IsIso ((moduleToHomotopy R D).map f)) (hM : moduleHomotopicallyProjective R D M) :
    moduleHomotopicallyProjective R D N := by
  let H := moduleToHomotopy R D
  let e := asIso (H.map f)
  obtain ⟨g, hg⟩ := H.map_surjective e.inv
  apply moduleHomotopicallyProjective_of_homotopyRetract R D g f _ hM
  rw [Functor.map_comp, hg]
  exact e.inv_hom_id.trans (H.map_id N).symm

variable {K : SSet.{max (u + 1) v}}
  {F : K ⟶ dgNerve R (RightModule R D)}
  (c : JoinCocone F)
  (hF : ∀ s : K _⦋0⦌, dgModuleProjectiveProperty R D ((F.app _ s).obj 0))
  (hc : dgModuleProjectiveProperty R D (c.vertex.obj 0))

/-- 元の図式の全単体を同じ射影的部分圏へ持ち上げる。 -/
def specifiedProjectiveDiagram : K ⟶ dgProjectiveModuleNerve R D :=
  fullInclusionLift R (RightModule R D) (dgModuleProjectiveProperty R D) F hF

/-- 元の同じ余錐を、頂点・脚・高次成分を保って持ち上げる。 -/
def specifiedProjectiveCocone : JoinCocone (specifiedProjectiveDiagram R D hF) := by
  let L := fullInclusionLift R (RightModule R D) (dgModuleProjectiveProperty R D)
    c.val (dgBarCocone_vertices R D c hF hc)
  refine ⟨L, ?_⟩
  apply (cancel_mono (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleProjectiveProperty R D)))).1
  rw [Category.assoc, fullInclusionLift_comp]
  change _ = fullInclusionLift R (RightModule R D) (dgModuleProjectiveProperty R D) F hF ≫ _
  rw [fullInclusionLift_comp]
  exact c.property

/-- 包含で戻した全単体的写像は、元の計算済み余錐そのもの。 -/
theorem specifiedProjectiveCocone_image :
    (specifiedProjectiveCocone R D c hF hc).val ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)) = c.val := by
  change fullInclusionLift R (RightModule R D) (dgModuleProjectiveProperty R D) c.val
    (dgBarCocone_vertices R D c hF hc) ≫ _ = _
  exact fullInclusionLift_comp R (RightModule R D) (dgModuleProjectiveProperty R D) _ _

/-- 同じ持ち上げた余錐は、元の余極限性を反映する。 -/
theorem specifiedProjectiveCocone_isColimit (h : IsColimitCone c) :
    IsColimitCone (specifiedProjectiveCocone R D c hF hc) := by
  apply isColimitCone_of_fullInclusion
  let d := fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
    (specifiedProjectiveCocone R D c hF hc)
  have he := fullInclusionLift_comp R (RightModule R D) (dgModuleProjectiveProperty R D) F hF
  apply (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff he d).mpr
  have hd : SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he d = c := by
    apply Subtype.ext
    rw [SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_val]
    change (specifiedProjectiveCocone R D c hF hc).val ≫ _ = c.val
    exact specifiedProjectiveCocone_image R D c hF hc
  rw [hd]
  exact h

/-- 一点加群の射影的模型から、既存D(A)への同じ全準圏同値。 -/
def projectivePointEquivalence (A : Type u) [CommRing A] :=
  (dgSemifreeToProjectiveNerve_isQCatEquivalence A PUnit.{1}).choose.symm.trans
    (semifreePointEquivalence A)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
