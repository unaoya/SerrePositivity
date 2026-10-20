module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativePrefixTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightAnodyneJoinPrefix
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRightCosliceSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeSectionFiber

/-!
概要：三角形・四面体の最後の頂点への余錐制限は、固定終点でも自明 Kan fibration。
方針：元の δ0 の right anodyne の合成と、coslice 制限の固定終点 fiber の充填性を使う。
規約：元の頂点座標と図式表示を保持。使われ方：同じ終端を持つ native 全図式族の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 三角形の最後の頂点の包含は、同じ δ0 の合成として right anodyne。 -/
lemma triangleTerminalVertex_rightAnodyne :
    rightAnodyneExtensions ((stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (0 : Fin 3)) :=
  rightAnodyneExtensions.comp_mem _ _ endpointInclusion_rightAnodyne
    triangleTerminalFace_rightAnodyne

/-- 四面体の最後の頂点の包含も、同じ元の三つの δ0 の合成として right anodyne。 -/
lemma tetrahedronTerminalVertex_rightAnodyne :
    rightAnodyneExtensions (((stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (0 : Fin 3)) ≫ stdSimplex.δ (0 : Fin 4)) :=
  rightAnodyneExtensions.comp_mem _ _ triangleTerminalVertex_rightAnodyne
    tetrahedronTerminalFace_rightAnodyne

/-- right anodyne な部分図式への正規化制限は、固定終点でも自明 Kan fibration。 -/
lemma normalizedCoconeRestrictionFiber_of_rightAnodyne {K L X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (i : L ⟶ K) [Mono i] (hi : rightAnodyneExtensions i)
    (s : L ⟶ X) (hs : i ≫ p = s) (y : X _⦋0⦌) :
    TrivialKanFibration (normalizedCoconeRestrictionFiber p i hs y) := by
  have := sliceUnderRestrict_trivialKanFibration p i hi
  have := cosliceRestrictionFiberMap_trivialKanFibration p i y
  rw [normalizedCoconeRestrictionFiber_eq]
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
