module

public import SerrePositivity.InfinityCategories.F1.Joins.HomotopyFatCone
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointLifting
public import SerrePositivity.InfinityCategories.F1.Joins.JoinEndpointMaps
public import SerrePositivity.InfinityCategories.Core.Limit

/-!
概要：定値始域からの指定ホモトピーを、元の図式と頂点を持つ native な錐へ実現する。
方針：fat join からの両端固定の比較を用い、指定円柱との可逆比較を保持する。
規約：錐の存在と極限性を区別する。元の図式を選び直さない。
使われ方：F1-4 の小さい全切断を頂点とする錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 元の変換から得る native な錐と、全円柱の両端固定比較。 -/
structure HomotopyConeRealization (H : SSet.Homotopy (SSet.const z) f) where
  cone : JoinCone f
  vertex_eq : cone.vertex = z
  comparison : SSet.Homotopy (fatJoinComparison Δ[0] K ≫ cone.val) (homotopyFatCone H)
  boundary : (fatJoinEndpointInclusion Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst (joinEndpointDiagram Δ[0] K) Δ[1] ≫ joinEndpointDesc (SSet.yonedaEquiv.symm z) f
  vertical_isInvertible : ∀ v,
    IsInvertibleEdge (simplicialHomotopyVertexEdge comparison v).toTruncated

/-- 指定された定値始域の変換を、同じ図式・頂点の native な錐へ実現する。 -/
def homotopyConeRealization [Quasicategory X]
    (H : SSet.Homotopy (SSet.const z) f) : HomotopyConeRealization H := Classical.choice <| by
  have hF : fatJoinEndpointInclusion Δ[0] K ≫ homotopyFatCone H =
      joinEndpointDesc (SSet.yonedaEquiv.symm z) f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a =>
      change (fatJoinInl Δ[0] K ≫ homotopyFatCone H).app n a =
        (SSet.yonedaEquiv.symm z).app n a
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (homotopyFatCone_inl H) n) a
    | inr a =>
      change (fatJoinInr Δ[0] K ≫ homotopyFatCone H).app n a = f.app n a
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (homotopyFatCone_inr H) n) a
  obtain ⟨G, hG, e, he, hI⟩ := exists_joinDiagram_of_fatJoinDiagram
    (joinEndpointDesc (SSet.yonedaEquiv.symm z) f) (homotopyFatCone H) hF
  have hGl : joinInl Δ[0] K ≫ G = SSet.yonedaEquiv.symm z := by
    have h := congrArg (fun q ↦ joinEndpointInl Δ[0] K ≫ q) hG
    rw [← Category.assoc, joinEndpointInl_inclusion] at h
    exact h
  have hGr : joinInr Δ[0] K ≫ G = f := by
    have h := congrArg (fun q ↦ joinEndpointInr Δ[0] K ≫ q) hG
    rw [← Category.assoc, joinEndpointInr_inclusion] at h
    exact h
  refine ⟨⟨⟨G, hGr⟩, ?_, e, he, hI⟩⟩
  rw [JoinCone.vertex_eq, hGl, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
