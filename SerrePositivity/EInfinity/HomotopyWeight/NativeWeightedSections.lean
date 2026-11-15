module
public import SerrePositivity.EInfinity.HomotopyWeight.ConeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：既存の重み付き錐の右随伴を、元のnativeな重み付き切断のendと同定する。
方針：同じ二つのテンソルの順序をbraidingで合わせ、右随伴の一意性を使う。
規約：IS-W2 R03a.1の既存構成の照合法則。重みの頂点や脚は変更しない。
使われ方：射影cofibrancyから元の切断空間のKan性を得る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

/-- 同じパラメーターと重みのテンソルの二つの順序の全自然同型。 -/
def coneSpaceParameterIso : WeightedCones.tensorDiagram I W ≅ weightedParameterFunctor W :=
  NatIso.ofComponents (fun K => NatIso.ofComponents (fun i => β_ K (W.obj i))
    (by intro i j f; simp; rfl)) (by
      intro X Y f
      apply NatTrans.ext
      funext i
      simp
      rfl)

/-- 元の錐の右随伴とnative endの指定された全自然同型。 -/
def coneSpaceNativeSectionsIso : WeightedCones.coneSpace I W ≅ weightedSectionsFunctor W :=
  Adjunction.rightAdjointUniq
    ((WeightedCones.adjunction I W).ofNatIsoLeft (coneSpaceParameterIso I W))
    (weightedSectionsAdjunction W)

/-- 元の射影cofibrant重みに対するnative切断空間はKan。 -/
theorem weightedSections_kanComplex_of_projective_cofibrant
    (hW : (boundaries I).rlp.llp (initial.to W))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SSet.KanComplex (weightedSections W H) := by
  have sourceKan := coneSpace_kanComplex I W hW H hH
  letI := sourceKan
  let e := (coneSpaceNativeSectionsIso I W).app H
  apply (isFibrant_iff (weightedSections W H)).2
  have ht : terminal.from (weightedSections W H) =
      e.inv ≫ terminal.from ((WeightedCones.coneSpace I W).obj H) := terminal.hom_ext _ _
  rw [ht]
  infer_instance

end SerrePositivity.EInfinity.HomotopyWeight
