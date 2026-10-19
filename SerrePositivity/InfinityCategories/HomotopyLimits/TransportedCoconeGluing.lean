module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBoundaryRectification

/-!
概要：部分余極限の比較辺と頂点輸送の合成が一致すれば、元の押し出し形状に実際の余錐を作る。
方針：輸送後の境界の Hom の計算を連結成分の一致へ戻し、単射側を厳密化して貼る。
規約：余極限性は共通部分に要求する。両側の頂点の輸送と比較射の具体的な選択を保持する。
使われ方：部分余極限対象の span の余錐から、元の coherent 図式の余錐への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 指定した元の余錐を、頂点の辺に沿って輸送した固定終点余錐空間の点。 -/
def transportedCoconeVertex {K : SSet.{u}} {F : K ⟶ X} (d : JoinCocone F)
    {y : X _⦋0⦌} (e : X.Edge d.vertex y) : (coconeMappingSpace F y) _⦋0⦌ :=
  (edgeTransport (sliceUnderProjection F) e).app (Opposite.op ⦋0⦌)
    (initialFiberVertexAt (sliceUnderProjection F) d d.vertex rfl)

/-- 二つの部分余錐の頂点輸送の合成の類が一致すれば、輸送後の境界は同じ連結成分にある。 -/
lemma transportedCocone_boundaries_component {A B C : SSet.{u}} {p : A ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c)
    (F : B ⟶ X) (i : A ⟶ B) (hi : i ≫ F = p) (dB : JoinCocone F)
    (G : C ⟶ X) (j : A ⟶ C) (hj : j ≫ G = p) (dC : JoinCocone G)
    {y : X _⦋0⦌} (eB : X.Edge dB.vertex y) (eC : X.Edge dC.vertex y)
    (h : SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc i F hi dB) ≫
        SSet.Truncated.HomotopyCategory.homMk eB.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc j G hj dC) ≫
        SSet.Truncated.HomotopyCategory.homMk eC.toTruncated) :
    SSet.π₀.mk ((normalizedCoconeRestrictionFiber F i hi y).app (Opposite.op ⦋0⦌)
        (transportedCoconeVertex dB eB)) =
      SSet.π₀.mk ((normalizedCoconeRestrictionFiber G j hj y).app (Opposite.op ⦋0⦌)
        (transportedCoconeVertex dC eC)) := by
  apply (coconeMappingSpacePiZeroEquiv c hc y).injective
  change coconeMappingSpacePiZeroEquiv c hc y
    (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi y)
      (SSet.mapπ₀ (edgeTransport (sliceUnderProjection F) eB)
        (SSet.π₀.mk (initialFiberVertexAt (sliceUnderProjection F) dB dB.vertex rfl)))) = _
  rw [coconeMappingSpacePiZeroEquiv_attachment_transport]
  change _ = coconeMappingSpacePiZeroEquiv c hc y
    (SSet.mapπ₀ (normalizedCoconeRestrictionFiber G j hj y)
      (SSet.mapπ₀ (edgeTransport (sliceUnderProjection G) eC)
        (SSet.π₀.mk (initialFiberVertexAt (sliceUnderProjection G) dC dC.vertex rfl))))
  rw [coconeMappingSpacePiZeroEquiv_attachment_transport]
  exact h

/-- 頂点での二つの合成の一致から、輸送した左余錐を保つ元の図式の実際の余錐を得る。 -/
lemma exists_cocone_glue_of_apex_composites {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hp : IsPushout f g i j) [Mono g] (p : D ⟶ X)
    (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
    (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
    {y : X _⦋0⦌} (eB : X.Edge dB.vertex y) (eC : X.Edge dC.vertex y)
    (h : SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc f (i ≫ p) rfl dB) ≫
        SSet.Truncated.HomotopyCategory.homMk eB.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
          (colimitAttachmentApexEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) ≫
        SSet.Truncated.HomotopyCategory.homMk eC.toTruncated) :
    ∃ e : JoinCocone p, ∃ c' : (coconeMappingSpace (j ≫ p) y) _⦋0⦌,
      e.restrict i = (transportedCoconeVertex dB eB).val ∧ e.restrict j = c'.val ∧
        e.vertex = y ∧ SSet.π₀.mk c' = SSet.π₀.mk (transportedCoconeVertex dC eC) := by
  have hπ := transportedCocone_boundaries_component c hc
    (i ≫ p) f rfl dB (j ≫ p) g (coconePushoutBoundary_eq hp p) dC eB eC h
  simp only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id] at hπ
  exact exists_cocone_glue_of_boundary_component hp p y
    (transportedCoconeVertex dB eB) (transportedCoconeVertex dC eC) hπ

end
end SerrePositivity.InfinityCategories.HomotopyLimits
