module
public import SerrePositivity.DifferentialGraded.Tensor.Fubini

/-! # bimodule合成の値における結合比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 実際の合成bimoduleを左加群として読むと、既存の左作用関手と一致する。 -/
lemma compose_leftAt_eq (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) :
    (compose A B C E P Q).leftAt b = leftAt A B C E P Q b := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (compose A B C E P Q).leftAt b) (G := leftAt A B C E P Q b) (fun _ => rfl)
  intro e e'
  change ((compose A B C E P Q).toFunctor.map e e' ≫
    moduleHomπ A B (rightAt A B C E P Q e) (rightAt A B C E P Q e') b) ≫ 𝟙 _ =
    Q.toFunctor.map e e' ≫
      BalancedTensor.rightHomMap A C (Q.rightAt e) (Q.rightAt e') (P.leftAt b)
  rw [Category.comp_id, compose_leftMap_π]

variable (F : Type t) [DGCategory A F] [Small.{u} E]

/-- 右端Fのsmallnessを要求しない、三つのbimoduleの結合比較の値。 -/
def associatorValueIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) :
    (compose A B E F (compose A B C E P Q) R).value b f ≅
      (compose A B C F P (compose A C E F Q R)).value b f :=
  eqToIso (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
      (compose_leftAt_eq A B C E P Q b)) ≪≫
    BalancedTensor.Fubini.iso A C E Q (R.rightAt f) (P.leftAt b)

end SerrePositivity.DifferentialGraded.BimoduleTensor
