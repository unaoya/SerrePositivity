module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeCommonNativeHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeEndInverseHomotopies

/-!
概要：path end の元の逆円柱を同じ共通成分の円柱へ接続する、左右の指定四辺の正方形。
方針：逆代表の類を保って合成同型を相殺し、指定四辺を関手単体集合で実現する。
規約：左右で同じ共通円柱と native 定値辺を使う。使われ方：共通 path end への貼り合わせ。
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
local notation "LI" => specifiedCoconeLeftEndInverseHomotopy hp p c hc dB hB dC y
local notation "RI" => specifiedCoconeRightEndInverseHomotopy hp p c hc dB dC hC y
local notation "IL" => specifiedCoconeLeftNativeIso hp p c hc dB hB dC y
local notation "IR" => specifiedCoconeRightNativeIso hp p c hc dB dC hC y
local notation "NL" => specifiedCoconeLeftNativeHomotopy hp p c hc dB hB dC y
local notation "NR" => specifiedCoconeRightNativeHomotopy hp p c hc dB dC hC y
local notation "H" => specifiedCoconeCommonNativeHomotopy hp p c hc dB hB dC y
local notation "N" => specifiedCoconeNativeRootHomPrecomposition hp p c hc dB dC y
local notation "cls(" K ")" => SSet.Truncated.HomotopyCategory.homMk
  (functorEdgeOfSimplicialHomotopy K)

/-- 左の元の逆円柱を下辺、同じ共通円柱を右辺、native 比較を左辺に保つ正方形。 -/
def specifiedCoconeLeftInverseNativeHomSquare :
    SerrePositivity.InfinityCategories.FunctorHomSquare LI (functorHomotopyRefl N) NL H :=
  Classical.choice (by
    apply nonempty_functorHomSquare_of_homEq
    rw [specifiedCoconeLeftEndInverseHomotopy_hom, specifiedCoconeCommonNativeHomotopy_hom,
      specifiedCoconeLeftNativeHomotopy_hom, functorHomotopyRefl_hom]
    change (functorIsoOfSimplicialHomotopy L).inv ≫
      ((functorIsoOfSimplicialHomotopy L).hom ≫ (IL).hom) = (IL).hom ≫ 𝟙 _
    simp only [Iso.inv_hom_id_assoc, Category.comp_id])

/-- 右の元の逆円柱にも、同じ右辺の共通円柱と同じ native 定値上辺を使う。 -/
def specifiedCoconeRightInverseNativeHomSquare :
    SerrePositivity.InfinityCategories.FunctorHomSquare RI (functorHomotopyRefl N) NR H :=
  Classical.choice (by
    apply nonempty_functorHomSquare_of_homEq
    have hH : cls(H) = cls(R) ≫ (IR).hom :=
      (specifiedCoconeCommonNativeHomotopy_hom hp p c hc dB hB dC y).trans
        (specifiedCoconeNativeEndHom_comp hp p c hc dB hB dC hC y)
    rw [specifiedCoconeRightEndInverseHomotopy_hom, hH,
      specifiedCoconeRightNativeHomotopy_hom, functorHomotopyRefl_hom]
    change (functorIsoOfSimplicialHomotopy R).inv ≫
      ((functorIsoOfSimplicialHomotopy R).hom ≫ (IR).hom) = (IR).hom ≫ 𝟙 _
    simp only [Iso.inv_hom_id_assoc, Category.comp_id])

end
end SerrePositivity.InfinityCategories.HomotopyLimits
