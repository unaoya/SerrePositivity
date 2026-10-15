module
public import SerrePositivity.DifferentialGraded.Bimodule.Transpose
public import SerrePositivity.DifferentialGraded.Bimodule.OfActions
public import SerrePositivity.DifferentialGraded.Tensor.Interchange

/-! # 相対tensorに残るbimoduleの二作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 値Q(c,e)⊗_C P(b,c)に残る右B作用。 -/
def rightAt (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) : RightModule A B :=
  P.transposeDG.comp (BalancedTensor.leftTensorDG A C (Q.rightAt e))

/-- 同じ値に残る左E作用。 -/
def leftAt (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) : LeftModule A E :=
  Q.toFunctor.comp (BalancedTensor.rightTensorDG A C (P.leftAt b))

/-- 残る二作用の交換は相対tensorの主Hom交換則から従う。 -/
lemma interchange (P : Bimodule A B C) (Q : Bimodule A C E)
    {b b' : Bᵒᵖ} {e e' : E} {p q : ℤ}
    (f : GradedHom A b b' p) (g : GradedHom A e e' q) :
    (((rightAt A B C E P Q e).map b b').f p f).comp
      (((leftAt A B C E P Q b'.unop).map e e').f q g)
        (by omega : p + q = q + p) =
    (q * p).negOnePow • ((((leftAt A B C E P Q b.unop).map e e').f q g).comp
      (((rightAt A B C E P Q e').map b b').f p f) rfl) := by
  have h := congrArg (fun t => (q * p).negOnePow • t)
    (BalancedTensor.homMaps_interchange A C
      ((Q.toFunctor.map e e').f q g) ((P.transposeHom b b').f p f) rfl)
  rw [smul_smul, Int.units_mul_self, one_smul] at h
  exact h.symm

/-- 左EのHomをパラメータにした全次数自然な右B加群変換。 -/
def paramTrans (P : Bimodule A B C) (Q : Bimodule A C E) (e e' : E) :
    ModuleParamTrans A B (e ⟶[Complex A] e')
      (rightAt A B C E P Q e) (rightAt A B C E P Q e') where
  app b := (leftAt A B C E P Q b.unop).map e e'
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y q p r n hn g f m
    have h := Cochain.congr_v (interchange A B C E P Q f g) r n (by omega)
    rw [Cochain.comp_v _ _ _ r (r + p) n rfl (by omega), Cochain.units_smul_v,
      Cochain.comp_v _ _ _ r (r + q) n rfl (by omega)] at h
    exact congrArg (fun t => t m) h

end SerrePositivity.DifferentialGraded.BimoduleTensor
