module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeEndHomotopies
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorHomSquareRealization

/-!
概要：共通 end の元の二円柱と公開した native 比較を四辺に持つ実際の正方形。
方針：同じ raw な円柱の合成則を同じ型付き端点へ移し、関手単体集合で実現する。
規約：四辺の代表を固定。使われ方：共通 path end への全族の比較。
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
local notation "IR" => specifiedCoconeRightNativeIso hp p c hc dB dC hC y
local notation "NL" => specifiedCoconeLeftNativeHomotopy hp p c hc dB hB dC y
local notation "NR" => specifiedCoconeRightNativeHomotopy hp p c hc dB dC hC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (functorEdgeOfSimplicialHomotopy H)

/-- 表示を揃えた元の HL・HR と同じ native 比較の積は、型付きの射として一致する。 -/
lemma specifiedCoconeNativeEndHom_comp : cls(L) ≫ (IL).hom = cls(R) ≫ (IR).hom := by
  have hL := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq L _
    (specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)
  have hR := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq R _
    (specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)
  have h := (arrowComposition_congr hL rfl).trans
    ((specifiedCoconeNativeHom_comp_hom_arrow hp p c hc dB hB dC hC y).trans
      (arrowComposition_congr hR rfl).symm)
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の二円柱と公開した native 円柱を四辺に保つ全パラメータの正方形が存在する。 -/
lemma nonempty_specifiedCoconeNativeEndHomSquare : Nonempty (SerrePositivity.InfinityCategories.FunctorHomSquare L NR R NL) := by
  apply nonempty_functorHomSquare_of_homEq
  rw [specifiedCoconeLeftNativeHomotopy_hom, specifiedCoconeRightNativeHomotopy_hom]
  exact specifiedCoconeNativeEndHom_comp hp p c hc dB hB dC hC y

/-- 指定四辺を持つ、全 Hom のパラメータ上の実際の関手正方形。 -/
def specifiedCoconeNativeEndHomSquare : SerrePositivity.InfinityCategories.FunctorHomSquare L NR R NL :=
  (nonempty_specifiedCoconeNativeEndHomSquare hp p c hc dB hB dC hC y).some

end
end SerrePositivity.InfinityCategories.HomotopyLimits
