module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightRestrictionPathElements
public import SerrePositivity.DifferentialGraded.Tensor.RightRestrictionValueHom
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

/-! # 右制限・結合子の二経路の固定成分関数による計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E T)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "RP" => Bimodule.rightRestriction A B D C F P₀

/-- 左経路の固定成分は、元の三重生成元をそのまま右括弧へ送る。 -/
lemma associatorRightRestriction_left_component_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    composeRightRestrictionValueComponent A B D C T F P₀ (compose A C E T Q₀ R₀) d t n
        (associatorValueComponent A D C E T RP Q₀ R₀ d t n
          (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn)) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h := associatorRightRestriction_left_path_element A B D C E T F P Q R
    d c e t τ q p hi hl hn
  rw [composeRightRestrictionValueComponent_eq, associatorValueComponent_eq]
  exact h

/-- 右経路の固定成分も同じ三重生成元を与える。 -/
lemma associatorRightRestriction_right_component_element (d : D) (c : C) (e : E) (t : T)
    {k r s i l n : ℤ} (τ : ((R₀).value e t).X k) (q : ((Q₀).value c e).X r)
    (p : ((P₀).value (F.obj d) c).X s) (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorValueComponent A B C E T P₀ Q₀ R₀ (F.obj d) t n
        (composeRightRestrictionValueComponent A B D E T F (compose A B C E P₀ Q₀) R₀ d t n
          (composeMapComponent A D E T (composeRightRestrictionIso A B D C E F P Q).hom
            (𝟙 R) d t n
              (associatorLeftElement A D C E T RP Q₀ R₀ d c e t τ q p hi hn))) =
      associatorRightElement A B C E T P₀ Q₀ R₀ (F.obj d) c e t τ q p hl (by omega) := by
  have h := associatorRightRestriction_right_path_element A B D C E T F P Q R
    d c e t τ q p hi hl hn
  rw [associatorValueComponent_eq, composeRightRestrictionValueComponent_eq,
    composeMapComponent_eq]
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
