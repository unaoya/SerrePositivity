module

public import SerrePositivity.EInfinity.Hammock.ColimitCompositionPointAssociativity
public import SerrePositivity.EInfinity.Hammock.ColimitIdentityPoint

/-!
# 元の一定の点による hammock の前後合成

概要：単位からの写像を元の豊穣合成の片側へ代入する。
方針：元の点の合成と全単体作用素を使う。
規約：全語の余極限上の既存の合成を保持する。
使われ方：指定射の前後合成のホモトピー逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y Z T : C}

def composeUnitMaps (p : 𝟙_ SSet.{max u v} ⟶ colimitGraph W X Y)
    (q : 𝟙_ SSet.{max u v} ⟶ colimitGraph W Y Z) :
    𝟙_ SSet.{max u v} ⟶ colimitGraph W X Z :=
  (λ_ (𝟙_ SSet.{max u v})).inv ≫ (p ⊗ₘ q) ≫ colimitComposition W X Y Z

def postcomposePointMap (X : C) (p : 𝟙_ SSet.{max u v} ⟶ colimitGraph W Y Z) :
    colimitGraph W X Y ⟶ colimitGraph W X Z :=
  (ρ_ (colimitGraph W X Y)).inv ≫ (𝟙 _ ⊗ₘ p) ≫ colimitComposition W X Y Z

def precomposePointMap (p : 𝟙_ SSet.{max u v} ⟶ colimitGraph W X Y) (Z : C) :
    colimitGraph W Y Z ⟶ colimitGraph W X Z :=
  (λ_ (colimitGraph W Y Z)).inv ≫ (p ⊗ₘ 𝟙 _) ≫ colimitComposition W X Y Z

lemma postcomposePointMap_comp (p : 𝟙_ SSet.{max u v} ⟶ colimitGraph W Y Z)
    (q : 𝟙_ SSet.{max u v} ⟶ colimitGraph W Z T) (X : C) :
    postcomposePointMap X p ≫ postcomposePointMap X q =
      postcomposePointMap X (composeUnitMaps p q) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact composePoint_assoc W x (p.app n PUnit.unit) (q.app n PUnit.unit)

lemma precomposePointMap_comp (p : 𝟙_ SSet.{max u v} ⟶ colimitGraph W X Y)
    (q : 𝟙_ SSet.{max u v} ⟶ colimitGraph W Y Z) (T : C) :
    precomposePointMap q T ≫ precomposePointMap p T =
      precomposePointMap (composeUnitMaps p q) T := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  exact (composePoint_assoc W (p.app n PUnit.unit) (q.app n PUnit.unit) x).symm

lemma postcomposePointMap_unit (X Y : C) :
    postcomposePointMap X (colimitUnit W Y) = 𝟙 (colimitGraph W X Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change composePoint W X Y Y x ((colimitUnit W Y).app n PUnit.unit) = x
  rw [← arrowPoint_identity]
  exact composePoint_identity_right W x

lemma precomposePointMap_unit (X Y : C) :
    precomposePointMap (colimitUnit W X) Y = 𝟙 (colimitGraph W X Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change composePoint W X X Y ((colimitUnit W X).app n PUnit.unit) x = x
  rw [← arrowPoint_identity]
  exact composePoint_identity_left W x

end SerrePositivity.EInfinity.Hammock
