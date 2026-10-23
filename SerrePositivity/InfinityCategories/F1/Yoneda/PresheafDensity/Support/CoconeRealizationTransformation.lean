module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationVertex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationFatHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.HomotopyCoconeRealization

/-!
概要：ホモトピーから実現した余錐の変換を、元の指定変換へ戻す。
方針：実現の両端固定比較を変換空間へ curry する。
規約：元の図式・指定頂点と全ホモトピーを保持する。
使われ方：全空間余錐と元の単位の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：実現した余錐の標準変換は元の指定変換にホモトピック。
方針：fat join 比較の両端と全時間の境界を照合して curry する。
規約：変換の族の実際のホモトピー。使われ方：単位との整合性。 -/
def coconeRealizationTransformationHomotopy
    (t : (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z))) _⦋0⦌)
    (R : HomotopyCoconeRealization
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated)) :
    SSet.Homotopy (SSet.yonedaEquiv.symm ((coconeTransformationMap f z).app _
      (coconeMappingPointAt R.cocone z R.vertex_eq))) (SSet.yonedaEquiv.symm t) := by
  let a := SSet.yonedaEquiv.symm ((coconeTransformationMap f z).app _
    (coconeMappingPointAt R.cocone z R.vertex_eq))
  let b := SSet.yonedaEquiv.symm t
  have ha : constantTransformationFatDiagram a =
      fatJoinComparison K Δ[0] ≫ R.cocone.val :=
    coconeTransformationPointAt_fatDiagram R.cocone z R.vertex_eq
  have hb : constantTransformationFatDiagram b = homotopyFatCocone
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated) :=
    constantTransformationFatDiagram_vertex t
  let H : SSet.Homotopy (constantTransformationFatDiagram a)
      (constantTransformationFatDiagram b) :=
    ⟨R.comparison.h, R.comparison.h₀.trans ha.symm, R.comparison.h₁.trans hb.symm, by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property⟩
  apply constantTransformationHomotopyOfFatDiagram a b H
  · change (fatJoinInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h = _
    have h := congrArg (fun q ↦ (joinEndpointInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ q)
      R.boundary
    rw [← Category.assoc, ← comp_whiskerRight, joinEndpointInl_fatInclusion,
      ← Category.assoc, whiskerRight_fst, Category.assoc] at h
    exact h
  · change (fatJoinInr K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h = _
    have h := congrArg (fun q ↦ (joinEndpointInr K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ q)
      R.boundary
    rw [← Category.assoc, ← comp_whiskerRight, joinEndpointInr_fatInclusion,
      ← Category.assoc, whiskerRight_fst, Category.assoc] at h
    change (fatJoinInr K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h =
      fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm z at h
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const] at h
    exact h

end SerrePositivity.InfinityCategories.F2
