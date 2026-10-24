module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeHomSquare
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionTriangle

/-!
概要：共通成分の一つの比較円柱を選び、元の左右の円柱との合成三角形を同時に固定する。
方針：左の指定合成同型を共通代表とし、左右の合成等式を三角形へ戻す。
規約：左右の元の円柱と native 比較は同じ代表を使う。使われ方：共通 path end の底の円柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "L" => specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "R" => specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y
local notation "IL" => specifiedCoconeLeftNativeIso hp p c hc dB hB dC y
local notation "NL" => specifiedCoconeLeftNativeHomotopy hp p c hc dB hB dC y
local notation "NR" => specifiedCoconeRightNativeHomotopy hp p c hc dB dC hC y
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "N" => specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y

/-- 共通成分の比較同型には、元の左 HL と公開した native 比較の同じ積を使う。 -/
def specifiedCoconeCommonNativeIso :
    FunctorIso (V ≫ coconeMappingSpaceHomComparison c hc y) N :=
  functorIsoOfSimplicialHomotopy L ≪≫ IL

/-- 左右の合成三角形に同時に用いる、共通成分の一つの実際の円柱。 -/
def specifiedCoconeCommonNativeHomotopy :
    SSet.Homotopy (V ≫ coconeMappingSpaceHomComparison c hc y) N :=
  (specifiedCoconeCommonNativeIso hp p c hc dB hB dC y).simplicialHomotopy
local notation "H" => specifiedCoconeCommonNativeHomotopy hp p c hc dB hB dC y

/-- 共通代表の類は元の左 HL と native 比較の指定積を保持する。 -/
lemma specifiedCoconeCommonNativeHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      (specifiedCoconeCommonNativeIso hp p c hc dB hB dC y).hom :=
  SerrePositivity.InfinityCategories.functorIso_simplicialHomotopy_hom _

/-- 左の元の二円柱と同じ共通代表を三辺に持つ実際の合成三角形。 -/
def specifiedCoconeLeftCommonNativeTriangle : FunctorCompositionTriangle L NL H :=
  Classical.choice (by
    apply nonempty_functorCompositionTriangle_of_homEq
    rw [specifiedCoconeLeftNativeHomotopy_hom, specifiedCoconeCommonNativeHomotopy_hom]
    rfl)

/-- 右の二円柱も、全く同じ共通代表を対角に持つ合成三角形で結ぶ。 -/
def specifiedCoconeRightCommonNativeTriangle : FunctorCompositionTriangle R NR H :=
  Classical.choice (by
    apply nonempty_functorCompositionTriangle_of_homEq
    rw [specifiedCoconeRightNativeHomotopy_hom, specifiedCoconeCommonNativeHomotopy_hom]
    exact (specifiedCoconeNativeEndHom_comp hp p c hc dB hB dC hC y).symm)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
