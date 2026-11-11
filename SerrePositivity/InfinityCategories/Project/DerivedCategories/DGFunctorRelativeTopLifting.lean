module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBoundaryAssembly
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # dg 関手に沿う最上位成分と境界の同時持ち上げ

概要：全射準同型な Hom 写像に沿って、既知境界と目標の最上位成分を同時に持ち上げる。
方針：Bianchi の閉性を複体の境界生成元の持ち上げ定理に渡す。
規約：対象の持ち上げは別工程。使われ方：β3 の分解の nerve の相対境界充填。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [DGCategory A E]

/-- 正しい目標成分と既知の境界を同時に持つ最上位の持ち上げが存在する。 -/
lemma dgFunctor_relative_top_lift (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : _root_.SerrePositivity.DifferentialGraded.HomQuasiIso F) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (he : ∀ I, I ≠ Finset.univ → s.Equation I)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card)
    (ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ))
    (r : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj (s.obj a)) (F.obj (s.obj b)) k)
    (hr : (F.map (s.obj a) (s.obj b)).f (k + 1)
      (s.rhs Finset.univ a b k hI ha hb hk) = _root_.SerrePositivity.DifferentialGraded.differential A r) :
    ∃ q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k,
      _root_.SerrePositivity.DifferentialGraded.differential A q = s.rhs Finset.univ a b k hI ha hb hk ∧
        (F.map (s.obj a) (s.obj b)).f k q = r := by
  have hz : _root_.SerrePositivity.DifferentialGraded.differential A (s.rhs Finset.univ a b k hI ha hb hk) = 0 := by
    apply s.differential_rhs_zero_of_proper_equations
    intro J hJ
    exact he J (Finset.ssubset_iff_subset_ne.mp hJ).2
  let z : _root_.SerrePositivity.DifferentialGraded.complexCycles A (homObject A D (s.obj a) (s.obj b)) (k + 1) :=
    ⟨s.rhs Finset.univ a b k hI ha hb hk, hz⟩
  exact _root_.SerrePositivity.DifferentialGraded.complex_boundary_lifting_of_surjective_quasiIso A (F.map (s.obj a) (s.obj b))
    (hs _ _) (hq _ _) k z r hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories
