module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.RightKanConeUniverseShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCounitUniverse

/-!
概要：元の二つの全錐間の指定ホモトピーを、同じ全錐の宇宙移送の間へ写す。
方針：既存の全円柱の移送を、既存の錐形状の逆宇宙同型で前合成する。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の任意の係数への反映。
規約：元の全族・図式の制限・固定頂点を保持し、独立な点ごとの同型で代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 指定した全錐間の同じホモトピーを、同じ両錐の宇宙移送の間へ写す。 -/
def coneHomotopyUlift {K D : SSet.{u}} {p q : K ⟶ D} {c : JoinCone p} {d : JoinCone q}
    (H : SSet.Homotopy c.val d.val) :
    SSet.Homotopy (JoinCone.ulift.{u, v} c).val (JoinCone.ulift.{u, v} d).val where
  h := ((uliftConeShapeIso.{u, v} K 0).inv ▷ (Δ[1] : SSet.{max u v})) ≫
    simplexTensorMap.{v} H.h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, simplexTensorMap_zero, H.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, simplexTensorMap_one, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 全錐のホモトピーの底の全射は、元の底の全射の同じ宇宙移送になる。 -/
lemma coneHomotopyUlift_boundary {K D : SSet.{u}} {p q : K ⟶ D}
    {c : JoinCone p} {d : JoinCone q} (H : SSet.Homotopy c.val d.val) :
    (joinInr (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ▷
      (Δ[1] : SSet.{max u v})) ≫ (coneHomotopyUlift.{u, v} H).h =
    simplexTensorMap.{v} ((joinInr (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ H.h) := by
  change (joinInr (Δ[0] : SSet.{max u v}) _ ▷ (Δ[1] : SSet.{max u v})) ≫
    ((uliftConeShapeIso.{u, v} K 0).inv ▷ (Δ[1] : SSet.{max u v})) ≫
      simplexTensorMap.{v} H.h = _
  rw [← Category.assoc, ← comp_whiskerRight, uliftConeShapeIso_inv_inr,
    simplexTensorMap_source]

/-- 元の頂点で時間に定値な全ホモトピーは、同じ宇宙移送の頂点でも時間に定値。 -/
lemma coneHomotopyUlift_fixedVertex {K D : SSet.{u}} {p q : K ⟶ D}
    {c : JoinCone p} {d : JoinCone q} (H : SSet.Homotopy c.val d.val)
    (hH : (joinInl (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ joinInl (Δ[0] : SSet.{u}) K ≫ c.val) :
    (joinInl (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ▷
      (Δ[1] : SSet.{max u v})) ≫ (coneHomotopyUlift.{u, v} H).h =
    fst (Δ[0] : SSet.{max u v}) (Δ[1] : SSet.{max u v}) ≫
      joinInl (Δ[0] : SSet.{max u v}) _ ≫ (JoinCone.ulift.{u, v} c).val := by
  change (joinInl (Δ[0] : SSet.{max u v}) _ ▷ (Δ[1] : SSet.{max u v})) ≫
    ((uliftConeShapeIso.{u, v} K 0).inv ▷ (Δ[1] : SSet.{max u v})) ≫
      simplexTensorMap.{v} H.h = _
  rw [← Category.assoc, ← comp_whiskerRight, uliftConeShapeIso_inv_inl,
    comp_whiskerRight, Category.assoc, simplexTensorMap_source, hH,
    simplexTensorMap_constant, whiskerRight_fst_assoc]
  have he := congrArg (fun f => f ≫ (SSet.uliftFunctor.{v, u}).map c.val)
    (uliftConeShapeIso_inv_inl.{u, v} K 0)
  have hh : (uliftStdSimplexIso.{u, v} 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[0] : SSet.{u}) K ≫ c.val) =
      joinInl (Δ[0] : SSet.{max u v}) _ ≫ (JoinCone.ulift.{u, v} c).val := by
    rw [Functor.map_comp]
    change (uliftStdSimplexIso.{u, v} 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[0] : SSet.{u}) K) ≫
      (SSet.uliftFunctor.{v, u}).map c.val =
      joinInl (Δ[0] : SSet.{max u v}) _ ≫
        ((uliftConeShapeIso.{u, v} K 0).inv ≫ (SSet.uliftFunctor.{v, u}).map c.val)
    simpa only [Category.assoc] using he.symm
  simpa only [Category.assoc] using congrArg
    (fun f => fst (Δ[0] : SSet.{max u v}) (Δ[1] : SSet.{max u v}) ≫ f) hh

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
