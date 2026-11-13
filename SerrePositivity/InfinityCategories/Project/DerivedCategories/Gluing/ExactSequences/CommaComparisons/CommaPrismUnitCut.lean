module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugPrismData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms

/-! 左係数が元の単位である切断は、符号付きの右比較 cochain そのものになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded

lemma dgGluingMappedUnitCompose_heq {R : Type u} [CommRing R]
    {A : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] {E : Type w} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A E) {x y : A} {z : E} {p q k : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R (H.obj y) z q) (h : p + q = k)
    (hxy : x = y) (hp : p = 0) (hf : HEq f (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val) (σ : ℤˣ) :
    HEq (σ • _root_.SerrePositivity.DifferentialGraded.compose R g ((H.map x y).f p f) h) (σ • g) := by
  cases hxy
  subst p
  have hk : k = q := by omega
  subst hk
  apply heq_of_eq
  rw [eq_of_heq hf, _root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement]
  exact congrArg (fun a => σ • a) (_root_.SerrePositivity.DifferentialGraded.compose_unit R g)

variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)

def dgGluingCommaPrismRightCorrection
    (I : Finset (Fin (n + 1))) (b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (j : Fin (n + 1)) (hj : j ∈ I) (hjb : j < b) :=
  ((I.filter (j < ·)).card : ℤ).negOnePow •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b)
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) (s.cutRight I b hI hb j hj hjb)

lemma dgGluingCommaPrismCut_of_left_unit
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hxy : s.obj a = s.obj j) (hp : 2 - ((I.filter (· ≤ j)).card : ℤ) = 0)
    (hf : HEq (s.cutLeft I a hI ha j hj haj) (_root_.SerrePositivity.DifferentialGraded.unitElement R (s.obj j)).val) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j hj haj hjb)
      (dgGluingCommaPrismRightCorrection R C E F s I b hI hb j hj hjb) := by
  exact dgGluingMappedUnitCompose_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F)
    (s.cutLeft I a hI ha j hj haj)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _
      (s.cutRight I b hI hb j hj hjb)) _ hxy hp hf _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
