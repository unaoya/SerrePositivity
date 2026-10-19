module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentPiZero

/-!
概要：付加で作った比較辺と、輸送した元の部分余錐の境界の Hom の値を直接照合する。
方針：正規化した制限の零単体を既存の比較の点と同定し、transport の後合成の式を使う。
規約：元の部分余錐・付加で作った射・選んだ transport を全てそのまま保持する。
使われ方：span の余錐の合成三角形を、境界の連結成分の貼り合わせ条件へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} [Quasicategory X] {p : A ⟶ X}
  (F : C ⟶ X) (i : A ⟶ C) (hi : i ≫ F = p) (d : JoinCocone F)

/-- 指定した部分余錐を制限した点は、付加による比較で用いた元の境界の点に一致する。 -/
lemma normalizedCoconeRestrictionFiber_vertex :
    (normalizedCoconeRestrictionFiber F i hi d.vertex).app (Opposite.op ⦋0⦌)
        (initialFiberVertexAt (sliceUnderProjection F) d d.vertex rfl) =
      colimitAttachmentFiberVertex i F hi d := by
  cases hi
  apply Subtype.ext
  rfl

/-- 輸送後の境界の Hom の値は、実際の部分余極限の比較辺と輸送辺の合成の類である。 -/
lemma coconeMappingSpacePiZeroEquiv_attachment_transport
    (c : JoinCocone p) (hc : IsColimitCone c) {y : X _⦋0⦌} (e : X.Edge d.vertex y) :
    coconeMappingSpacePiZeroEquiv c hc y
        (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi y)
          (SSet.mapπ₀ (edgeTransport (sliceUnderProjection F) e)
            (SSet.π₀.mk (initialFiberVertexAt (sliceUnderProjection F) d d.vertex rfl)))) =
      SSet.Truncated.HomotopyCategory.homMk (colimitAttachmentApexEdge c hc i F hi d) ≫
        SSet.Truncated.HomotopyCategory.homMk e.toTruncated := by
  rw [coconeMappingSpacePiZeroEquiv_restrict_transport, SSet.mapπ₀_mk,
    normalizedCoconeRestrictionFiber_vertex, coconeMappingSpacePiZeroEquiv_attachment]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
