module
public import SerrePositivity.DifferentialGraded.Module.Basic

/-! # 左dg加群と二重opposite

既存の共変豊穣関手LeftModuleを保持し、Dᵒᵖ上の右加群と比較する。
二重oppositeの合成比較は対称braidingの二乗から得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 二重oppositeでは二つのKoszul交換が打ち消し合う。 -/
lemma doubleOpposite_composition (x y z : D) :
    eComp (Complex A) (op (op x)) (op (op y)) (op (op z)) =
      eComp (Complex A) x y z := by
  rw [eComp_op_eq, eComp_op_eq]
  change (β_ (x ⟶[Complex A] y) (y ⟶[Complex A] z)).hom ≫
    (β_ (y ⟶[Complex A] z) (x ⟶[Complex A] y)).hom ≫ eComp (Complex A) x y z = _
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- Dから二重oppositeへの恒等Homを持つdg関手。 -/
def dgDoubleOpposite : DGFunctor A D Dᵒᵖᵒᵖ where
  obj x := op (op x)
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp x y z := by
    simp [doubleOpposite_composition]

/-- 二重oppositeからDへの恒等Homを持つdg関手。 -/
def dgDoubleUnop : DGFunctor A Dᵒᵖᵒᵖ D where
  obj x := x.unop.unop
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp x y z := by
    simpa using
      doubleOpposite_composition A D x.unop.unop y.unop.unop z.unop.unop

namespace LeftModule
variable {A D}

/-- 左加群をDᵒᵖ上の右加群として読む。 -/
def toRightOpposite (M : LeftModule A D) : RightModule A Dᵒᵖ :=
  (dgDoubleUnop A D).comp M

/-- Dᵒᵖ上の右加群を元の共変豊穣関手へ戻す。 -/
def ofRightOpposite (M : RightModule A Dᵒᵖ) : LeftModule A D :=
  (dgDoubleOpposite A D).comp M.toFunctor

@[simp] lemma of_toRightOpposite (M : LeftModule A D) :
    ofRightOpposite (toRightOpposite M) = M := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp [ofRightOpposite, toRightOpposite, DGFunctor.comp,
    dgDoubleOpposite, dgDoubleUnop, EnrichedFunctor.comp]

@[simp] lemma to_ofRightOpposite (M : RightModule A Dᵒᵖ) :
    toRightOpposite (ofRightOpposite M) = M := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp [ofRightOpposite, toRightOpposite, DGFunctor.comp,
    dgDoubleOpposite, dgDoubleUnop, EnrichedFunctor.comp]

end LeftModule

/-- 対象データの比較。射は後続で全次数自然性のHomを使う。 -/
def leftModuleEquivRightOpposite : LeftModule A D ≃ RightModule A Dᵒᵖ where
  toFun := LeftModule.toRightOpposite
  invFun := LeftModule.ofRightOpposite
  left_inv := LeftModule.of_toRightOpposite
  right_inv := LeftModule.to_ofRightOpposite

end SerrePositivity.DifferentialGraded
