module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramNormalizedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber

/-!
概要：元の全図式族の底を固定終点 fiber で表示し、正規化した面の制限を厳密に保つ。
方針：fiber 包含後の底と正規化制限の可換性を使う。
規約：元の図式と全族を保持。使われ方：付加辺面と native な三角形全族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K E B T : SSet.{u}} (q : E ⟶ B) (t : K ⟶ E) (y : B _⦋0⦌)
  (a : T ⟶ sliceUnder t) (ha : (a ≫ sliceUnderProjection t) ≫ q = SSet.const y)

include ha in
/-- 元の底の図式族は、同じ固定終点 y 上に留まる。 -/
lemma diagramBaseFiberFamily_fixed :
    (a ≫ sliceUnderPostcomp t q) ≫ sliceUnderProjection (t ≫ q) = SSet.const y := by
  rw [Category.assoc, sliceUnderPostcomp_projection]
  exact ha

/-- 元の全図式族の底を、同じ固定終点 fiber に表示する。 -/
def diagramBaseFiberFamily : T ⟶ coconeMappingSpace (t ≫ q) y :=
  vertexFiberLift (sliceUnderProjection (t ≫ q)) y (a ≫ sliceUnderPostcomp t q)
    (diagramBaseFiberFamily_fixed q t y a ha)

/-- fiber 包含後は、同じ元の全図式族の底そのものである。 -/
lemma diagramBaseFiberFamily_ι :
    diagramBaseFiberFamily q t y a ha ≫ vertexFiberι (sliceUnderProjection (t ≫ q)) y =
      a ≫ sliceUnderPostcomp t q := vertexFiberLift_ι _ _ _ _

/-- 正規化した部分図式の底は、元の底の固定終点族を同じ面へ制限したものに一致する。 -/
lemma diagramBaseFiberFamily_restrict {L : SSet.{u}} (i : L ⟶ K) (s : L ⟶ E)
    (hs : i ≫ t = s) :
    diagramBaseFiberFamily q s y (a ≫ normalizedCoconeRestriction t i hs)
        (initialDiagramNormalizedRestriction_fixed q t i s hs y a ha) =
      diagramBaseFiberFamily q t y a ha ≫ normalizedCoconeRestrictionFiber (t ≫ q) i
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hs)) y := by
  apply vertexFiber_hom_ext (sliceUnderProjection (s ≫ q)) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  rw [diagramBaseFiberFamily_ι, ← Category.assoc, diagramBaseFiberFamily_ι]
  exact normalizedCoconeRestriction_postcomp_family t i s hs q a

end
end SerrePositivity.InfinityCategories.HomotopyLimits
