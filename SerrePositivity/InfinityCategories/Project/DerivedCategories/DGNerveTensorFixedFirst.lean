module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorProductMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedFront
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：第一入力を固定した実 tensor 写像を、元の第二因子の dg 包含の nerve へ同定する。
方針：定値入力の非空切断を消し、同じ単位辺と空切断の実 cochain を使う。
規約：全単体・全面・退化を保持する。使われ方：二変数 Hom と既存 Hom の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators _root_.Simplicial
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveSelectedCutHom_constant_nonempty {n : ℕ} (x : B)
    (a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) (hab : a < b)
    (hc : ∀ j ∈ S, a < j ∧ j < b) (hS : S.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      a b S hab hc = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_zero
  have hcard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutIndex_card S a b hab hc
  have hpos := Finset.card_pos.mpr hS
  omega
/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveTensorCutTerm_constant_first_nonempty {n : ℕ} (x : B) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) (hab : a < b) (hS : S.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      t I a b S k hk hI ha hb hc = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_eq_selected R B C _ t I a b S k hk hI ha hb hc hab,
    dgNerveSelectedCutHom_constant_nonempty R B x a b S hab (fun j hj => (hc j hj).2) hS]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_left, smul_zero]
/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveTensorHomCandidate_constant_first_eq_empty {n : ℕ} (x : B) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      t I a b k hk hI ha hb =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
      t I a b ∅ k hk hI ha hb (by simp) := by
  let T := I.filter (fun j => a < j ∧ j < b)
  let E : T.powerset := ⟨∅, by simp⟩
  let F := fun S : T.powerset => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
    t I a b S.val k hk hI ha hb
    (fun j hj => Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj))
  change (∑ S, F S) = F E
  refine Finset.sum_eq_single_of_mem E (Finset.mem_univ E) ?_
  intro S _ hS
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C _ t I a b S.val k hk hI ha hb _ = 0
  apply dgNerveTensorCutTerm_constant_first_nonempty R B C x t I a b S.val k hk hI ha hb _ hab
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  apply hS
  exact Subtype.ext he

/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveConstant_edgeHom {n : ℕ} (x : B) (a b : Fin (n + 1)) (hab : a < b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData.edgeHom
      a b hab = (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_unit x {a, b} a b 0 _ _ _ _
    (by simp [ne_of_lt hab])
/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveTensorSimplex_constant_first {n : ℕ} (x : B) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex R B C
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n) t =
      t.map (_root_.SerrePositivity.DifferentialGraded.dgTensorIncludeSecond R B C x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
    (s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex R B C
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n) t).toSimplexData)
    (t := (t.map (_root_.SerrePositivity.DifferentialGraded.dgTensorIncludeSecond R B C x)).toSimplexData) rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have haI : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbI : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by
    rw [ha, hb]
    exact I.min'_lt_max'_of_card (by omega)
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
    t.toSimplexData I a b k hk hI haI hbI =
    (_root_.SerrePositivity.DifferentialGraded.dgTensorSecondHom R B C x (t.obj a) (t.obj b)).f k (t.hom I a b k hI ha hb hk)
  rw [dgNerveTensorHomCandidate_constant_first_eq_empty R B C x t.toSimplexData
    I a b k hk hI haI hbI hab,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_empty R B C _ t.toSimplexData I a b k hk hI haI hbI hab,
    dgNerveConstant_edgeHom R B x a b hab, _root_.SerrePositivity.DifferentialGraded.dgTensorSecondHom_apply]

open CartesianMonoidalCategory
/-- 元の固定入力における全単体作用の照合。 -/
lemma dgNerveTensorProductMap_second (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (x : B) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorProductMap R B E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeSecond R B E x) := by
  ext n t
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSimplex R B E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n.unop.len) t =
      t.map (_root_.SerrePositivity.DifferentialGraded.dgTensorIncludeSecond R B E x)
  exact dgNerveTensorSimplex_constant_first R B E x t

end SerrePositivity.InfinityCategories.Project.DerivedCategories
