module
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedMapFamily

/-! # 全Hom自然な閉零射を持つbimoduleの圏 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 対象は既存のbimodule、射は全Hom自然な閉零射。 -/
def BimoduleCategory := Bimodule A B C

namespace BimoduleCategory

/-- 既存のbimoduleを閉零射の圏の対象として読む。 -/
def of (M : Bimodule A B C) : BimoduleCategory A B C := M

/-- 閉零射の圏の対象から元のbimoduleを取り出す。 -/
def underlying (M : BimoduleCategory A B C) : Bimodule A B C := M

instance category : Category (BimoduleCategory A B C) where
  Hom M N := Bimodule.ClosedMapFamily A B C (underlying A B C M) (underlying A B C N)
  id M := Bimodule.closedMapFamilyId A B C (underlying A B C M)
  comp a b := Bimodule.closedMapFamilyComp A B C a b
  id_comp := by
    intro M N a
    apply Subtype.ext
    funext c
    exact Category.id_comp (a.val c)
  comp_id := by
    intro M N a
    apply Subtype.ext
    funext c
    exact Category.comp_id (a.val c)
  assoc := by
    intro M N P Q a b d
    apply Subtype.ext
    funext c
    exact Category.assoc (a.val c) (b.val c) (d.val c)

/-- 閉零射を元のMathlib GradedNatTransへ戻す。 -/
def homEquiv (M N : BimoduleCategory A B C) :
    (M ⟶ N) ≃ BimoduleParamTrans A B C (𝟙_ (Complex A)) (underlying A B C M) (underlying A B C N) :=
  (Bimodule.closedMapFamilyEquiv A B C (underlying A B C M) (underlying A B C N)).symm

end BimoduleCategory
end SerrePositivity.DifferentialGraded
