module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismData
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms

/-! 左係数が元の単位である切断は、符号付きの右比較 cochain そのものになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve

lemma dgGluingMappedUnitCompose_heq {R : Type u} [CommRing R]
    {A : Type v} [DGCategory R A] {E : Type w} [DGCategory R E]
    (H : DGFunctor R A E) {x y : A} {z : E} {p q k : ℤ}
    (f : GradedHom R x y p) (g : GradedHom R (H.obj y) z q) (h : p + q = k)
    (hxy : x = y) (hp : p = 0) (hf : HEq f (unitElement R y).val) (σ : ℤˣ) :
    HEq (σ • compose R g ((H.map x y).f p f) h) (σ • g) := by
  cases hxy
  subst p
  have hk : k = q := by omega
  subst hk
  apply heq_of_eq
  rw [eq_of_heq hf, DGFunctor.map_unitElement]
  exact congrArg (fun a => σ • a) (compose_unit R g)

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)

def dgGluingCommaPrismRightCorrection
    (I : Finset (Fin (n + 1))) (b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (hb : b = I.max' (Index.nonempty hI)) (j : Fin (n + 1)) (hj : j ∈ I) (hjb : j < b) :=
  ((I.filter (j < ·)).card : ℤ).negOnePow •
    dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b)
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) (s.cutRight I b hI hb j hj hjb)

lemma dgGluingCommaPrismCut_of_left_unit
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hxy : s.obj a = s.obj j) (hp : 2 - ((I.filter (· ≤ j)).card : ℤ) = 0)
    (hf : HEq (s.cutLeft I a hI ha j hj haj) (unitElement R (s.obj j)).val) :
    HEq (dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j hj haj hjb)
      (dgGluingCommaPrismRightCorrection R C E F s I b hI hb j hj hjb) := by
  exact dgGluingMappedUnitCompose_heq (dgCommaAugmentationSource R C E F)
    (s.cutLeft I a hI ha j hj haj)
    (dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.cutRight I b hI hb j hj hjb)) _ hxy hp hf _

end SerrePositivity.InfinityCategories
