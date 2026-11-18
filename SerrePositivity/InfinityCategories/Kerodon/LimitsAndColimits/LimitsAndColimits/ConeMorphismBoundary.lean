module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeMorphismApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCounitMorphismNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HoConstantMap

/-!
概要：元の錐圏の射は底で恒等射になり、指定余単位を頂点射で可換にする。
方針：全錐の底射影の定値性と端点移送の合成則を使う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の極限錐の比較。
規約：同じ底を固定した元の錐圏の射を用い、頂点の射を取り替えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ図式上の元の錐の射を底へ制限すると、指定した図式の恒等射になる。 -/
lemma coneHoMorphismValue_boundary {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (β : (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶
      SSet.HomotopyCategory.mk d) :
    kanFunctorHomCongr c.property d.property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) K)).app X)).toFunctor.map
        (coneHoMorphismValue β)) = 𝟙 (SSet.HomotopyCategory.mk (functorVertex p)) := by
  change hoHomMapWithVertexEqualities (coneRestriction K X)
    (congrArg functorVertex c.property) (congrArg functorVertex d.property)
    (hoHomMapWithVertexEqualities (coneValueProjection p)
      (coneValueProjection_vertex p c) (coneValueProjection_vertex p d) β) = _
  rw [hoHomMapWithVertexEqualities_comp]
  have h := hoHomMapWithVertexEqualities_congr (coneValueProjection_boundary p)
    ((congrArg ((coneRestriction K X).app (Opposite.op ⦋0⦌))
      (coneValueProjection_vertex p c)).trans (congrArg functorVertex c.property))
    ((congrArg ((coneRestriction K X).app (Opposite.op ⦋0⦌))
      (coneValueProjection_vertex p d)).trans (congrArg functorVertex d.property)) rfl rfl β
  apply h.trans
  simp only [hoHomMapWithVertexEqualities, hoConstantMap_hom,
    Category.id_comp, eqToHom_trans, eqToHom_refl]
  change (𝟙 (SSet.HomotopyCategory.mk (functorVertex p))) ≫
    (𝟙 (SSet.HomotopyCategory.mk (functorVertex p))) = _
  exact Category.id_comp _

/-- 元の錐の射による頂点射は、二つの指定余単位を可換にする。 -/
lemma coneCounitHom_coneMorphism {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (β : (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶
      SSet.HomotopyCategory.mk d) :
    constantFunctorHomMap K ((hoFunctor.map (sliceOverProjection p)).toFunctor.map β) ≫
      coneCounitHom d = coneCounitHom c := by
  have h := coneCounitHom_morphism_naturality c d (coneHoMorphismValue β)
  rw [coneHoMorphismValue_apex, coneHoMorphismValue_boundary, Category.comp_id] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
