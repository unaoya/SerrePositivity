module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationHomotopy
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTransformationFatDiagram

/-!
概要：両端固定の fat join 図式のホモトピーを定値変換空間へ移す。
方針：比較を円柱で制限し、固定した二端を全時間で保って curry する。
規約：時間ごとの存在へ弱めず、一本の全ホモトピーを構成する。
使われ方：native な余錐空間の比較のホモトピー右逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：同じ図式・終点を固定した fat join の変形は変換の族のホモトピーを与える。
方針：全円柱への制限の二端を計算し、円柱のホモトピーを変換空間へ戻す。
規約：標的の充填性は不要。使われ方：join の回収の比較を元の変換に戻す。 -/
def constantTransformationHomotopyOfFatDiagram
    (a b : T ⟶ intervalMappingSpace (functorVertex f) (functorVertex (SSet.const z)))
    (H : SSet.Homotopy (constantTransformationFatDiagram a) (constantTransformationFatDiagram b))
    (hf : (fatJoinInl K T ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ f)
    (hz : (fatJoinInr K T ▷ (Δ[1] : SSet.{u})) ≫ H.h = SSet.const z) :
    SSet.Homotopy a b := by
  let R := (fatJoinCylinder K T ▷ (Δ[1] : SSet.{u})) ≫ H.h
  have hR₀ : SSet.ι₀ ≫ R = constantTransformationPrism a := by
    dsimp only [R]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀,
      constantTransformationFatDiagram_cylinder]
  have hR₁ : SSet.ι₁ ≫ R = constantTransformationPrism b := by
    dsimp only [R]
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁,
      constantTransformationFatDiagram_cylinder]
  let H' : SSet.Homotopy (constantTransformationPrism a) (constantTransformationPrism b) :=
    ⟨R, hR₀, hR₁, by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property⟩
  apply constantTransformationHomotopyOfPrisms a b H'
  · change ((SSet.ι₀ ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ R = _
    dsimp only [R]
    rw [← Category.assoc, ← comp_whiskerRight, fatJoinCylinder_zero,
      comp_whiskerRight, Category.assoc, hf, ← Category.assoc, whiskerRight_fst, Category.assoc]
  · change ((SSet.ι₁ ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ R = _
    dsimp only [R]
    rw [← Category.assoc, ← comp_whiskerRight, fatJoinCylinder_one,
      comp_whiskerRight, Category.assoc, hz, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
