module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanActualIndexTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitRestrictionValue
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction

/-!
概要：同じ添字の実射から得た制限錐の極限比較は頂点の恒等射を誘導する。
方針：同じ制限錐とその頂点等式で、指定極限比較を計算する。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定輸送の比較。
使われ方：S8 の指定局所極限の値の計算。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

local instance actualIndexProjectionLeft {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (v : C _⦋0⦌) : LeftFibration (rightKanProjection δ v) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm v)))⟩

local instance actualIndexQuasicategory {K C : SSet.{u}} [Quasicategory K] [Quasicategory C]
    (δ : K ⟶ C) (v : C _⦋0⦌) : Quasicategory (rightKanShape δ v) :=
  quasicategory_of_innerFibration (rightKanProjection δ v)

/-- 同じ添字の実射から得た制限錐の極限比較は頂点の恒等射を誘導する。 -/
@[cite HTT "5.1.5.6" (partial := special) "右 Kan 輸送の同じ指定局所極限に沿う順射の計算。"]
lemma rightKan_actualIndexArrow_valueHom :
∀ {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
 {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
 (β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌),
let p := sliceUnderProjection (SSet.yonedaEquiv.symm v)
let b := (e.postcomp G).hom ≫
 Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
∀ (a : rightKanShape δ v ⟶ rightKanShape δ' v)
 (ha : a ≫ rightKanProjection δ' v = rightKanProjection δ v)
 (l : FunctorIso (pullback.fst p δ) (a ≫ pullback.fst p δ'))
 (hl : HEq (l.postcomp p) (e.precomp (rightKanProjection δ v)))
 (s : RightKanConeTransport δ O G (functorHomHomotopy b) v)
 (t : RightKanConeTransport δ' O G β v),
let he : a ≫ rightKanDiagram δ' O v = rightKanDiagram δ O v := by
 dsimp only [rightKanDiagram]; rw [← Category.assoc, ha]
let d := (restrictJoinCone t.cone a).cast he
∀ (ea : IsQCatEquivalence a) (hs : IsLimitCone s.cone) (ht : IsLimitCone t.cone),
 eqToHom (congrArg HomotopyCategory.mk s.cone_vertex.symm) ≫
   (limitVertexIsoOfOverEquivalence a ea ha O s.cone t.cone hs ht).hom ≫
   eqToHom (congrArg HomotopyCategory.mk t.cone_vertex) =
   𝟙 (HomotopyCategory.mk (G.app _ v)) := by
  intro K C D hK hC hD δ δ' e O G β v
  dsimp only
  intro a ha l hl s t
  let w : a ≫ rightKanDiagram δ' O v = rightKanDiagram δ O v := by
    rw [rightKanDiagram, rightKanDiagram, ← Category.assoc, ha]
  let t' := (restrictJoinCone t.cone a).cast w
  intro ea hs ht
  have ht' : IsLimitCone t' := ((isLimitCone_iff_restrict_equivalentShape a ea t.cone).mp ht).cast w
  obtain ⟨k, hk⟩ := rightKan_actualIndexArrow_transportConeIso e O G β v a ha l hl s t
  have hcmp : (limitVertexIso s.cone t' hs ht').hom =
      (hoFunctor.map (sliceOverProjection (rightKanDiagram δ O v))).toFunctor.map k.hom := by
    unfold limitVertexIso
    change (hoFunctor.map (sliceOverProjection (rightKanDiagram δ O v))).toFunctor.map
      (limitConeIso s.cone t' hs ht').hom =
      (hoFunctor.map (sliceOverProjection (rightKanDiagram δ O v))).toFunctor.map k.hom
    exact congrArg _ (ht'.isTerminalHo.hom_ext _ _)
  rw [limitVertexIsoOfOverEquivalence_hom_restriction
    (rightKanProjection δ v) (rightKanProjection δ' v) a ha ea O s.cone t.cone hs ht ht']
  rw [hcmp]
  simpa only [Category.assoc, eqToHom_trans] using hk

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
