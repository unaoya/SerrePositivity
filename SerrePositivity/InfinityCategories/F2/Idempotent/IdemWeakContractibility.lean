module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemConeRetraction
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransHomotopy
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeFamilyUnderlying
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakReverseHomotopy

/-!
概要：元の全 Idem の単体集合は弱可縮。
方針：元の吸収元の自然変換を、恒等から元の定値図式への全ホモトピーへ移す。
規約：元の Idem の Kan 性や全境界の充填性は仮定しない。
使われ方：HTT 4.4.5.10〜11 の元の包含の cofinal 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の吸収元は、元の恒等図式から元の一点への実際の全ホモトピーを与える。 -/
def idemShapeContraction :
    SSet.Homotopy (𝟙 IdemShape.{u}) (SSet.const (nerveVertex walkingObject)) := by
  have h := SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy walkingIdemCocone.{u}.ι
  rw [SerrePositivity.InfinityCategories.F1B.nerveMap_const] at h
  exact h

/-- 元の全 Idem は、全 Kan 標的へのホモトピー類で検査した意味で弱可縮。 -/
lemma idemShape_isWeaklyContractible : IsWeaklyContractible IdemShape.{u} := by
  let g : (⊤_ SSet.{u}) ⟶ IdemShape := SSet.const (nerveVertex walkingObject)
  apply isWeakHomotopyEquivalence_of_reverseHomotopyInverse (terminal.from IdemShape) g
  · change SSet.Homotopy (𝟙 IdemShape) (_ ≫ SSet.const _)
    rw [SSet.comp_const]
    exact idemShapeContraction
  · have h : g ≫ terminal.from IdemShape = 𝟙 _ := terminal.hom_ext _ _
    rw [h]
    exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))

end SerrePositivity.InfinityCategories.F2.Idempotent
