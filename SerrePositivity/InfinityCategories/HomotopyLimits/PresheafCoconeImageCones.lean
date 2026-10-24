module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoconeFlip
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の定義域全錐を指定前層余錐の交換評価で写し、底と余錐頂点の両像を回収する。
方針：元の全錐をそのまま写し、底制限と頂点評価を元の厳密な交換式で計算する。
規約：有限性・極限性を仮定せず、元の全錐・全脚・指定余錐を保持する。
使われ方：前層余極限頂点の実際の有限錐像を、元の全評価余錐の族と結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C K : SSet.{u}}
  {r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C}
  (q : JoinCocone r) {p : K ⟶ C.op} (c : JoinCone p)

/-- 元の定義域全錐を、同じ元の指定余錐の全評価余錐の族へ写す。 -/
def presheafCoconeImageCone :
    JoinCone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeFlip q) :=
  mapJoinCone (presheafCoconeFlip q) (JoinCone.ulift.{u, u + 1} c)

/-- 頂点評価による元の底図式は、元の指定余錐の頂点関手で写した図式そのもの。 -/
lemma presheafCoconeImageDiagram_apex :
    evaluateFunctorDiagram ((SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeFlip q)
      (coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B)) =
        (SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeVertexFunctor q := by
  rw [evaluateFunctorDiagram, Category.assoc, presheafCoconeFlip_apex]

/-- 同じ元の全錐の右頂点評価は、実際の余錐頂点関手で写した元の全錐そのもの。 -/
lemma presheafCoconeImageCone_apex :
    (evaluateFunctorCone (presheafCoconeImageCone q c)
      (coconeRightApexVertex ((SSet.uliftFunctor.{u + 1, u}).obj B))).cast
        (presheafCoconeImageDiagram_apex q) =
          mapJoinCone (presheafCoconeVertexFunctor q) (JoinCone.ulift.{u, u + 1} c) := by
  apply Subtype.ext
  change ((JoinCone.ulift.{u, u + 1} c).val ≫ presheafCoconeFlip q) ≫ _ = _
  rw [Category.assoc, presheafCoconeFlip_apex]
  rfl

/-- 元の底制限図式は、同じ元の前層図式の交換評価で写した底図式。 -/
lemma presheafCoconeImageDiagram_restriction :
    ((SSet.uliftFunctor.{u + 1, u}).map p ≫ presheafCoconeFlip q) ≫
      (pre (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[0])).app SpaceInfinity.{u} =
        (SSet.uliftFunctor.{u + 1, u}).map p ≫ internalHomFlipHomEquiv _ _ _ r := by
  rw [Category.assoc, presheafCoconeFlip_restriction]

/-- 元の全錐の底制限は、同じ元の前層図式の交換評価で写した元の全錐そのもの。 -/
lemma presheafCoconeImageCone_restriction :
    (mapJoinCone
      ((pre (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[0])).app SpaceInfinity.{u})
      (presheafCoconeImageCone q c)).cast (presheafCoconeImageDiagram_restriction q) =
        mapJoinCone (internalHomFlipHomEquiv _ _ _ r) (JoinCone.ulift.{u, u + 1} c) := by
  apply Subtype.ext
  change ((JoinCone.ulift.{u, u + 1} c).val ≫ presheafCoconeFlip q) ≫ _ = _
  rw [Category.assoc, presheafCoconeFlip_restriction]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
