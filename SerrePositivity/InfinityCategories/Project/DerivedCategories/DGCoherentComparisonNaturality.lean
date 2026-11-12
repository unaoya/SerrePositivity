module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplexComponentExt
/-!
概要：coherent 比較写像は dg 関手の全次数の作用に自然である。
方針：立方体の全旗の符号付き和への線形写像の作用を計算する。
規約：Small 仮定なしに元の対象・向き・全成分を保持する。
使われ方：coherent 合成 prism の固定標的 slice への自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

lemma dgCoherentCubeComponent_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    (Q.map (s.obj (.mk a)) (s.obj (.mk b))).f (-(S.card : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent (s.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor.dgStandardEnrichedFunctor Q)) hab S := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul]
  apply congrArg ((Equiv.Perm.sign σ : ℤ) • ·)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_component (Q.map _ _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (σ.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S))))
    Finset.univ (-(S.card : ℤ)) Finset.univ_nonempty (by simp)).symm

lemma dgCoherentCubeComponentAt_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) (k : ℤ) (hk : k = -(S.card : ℤ)) :
    (Q.map (s.obj (.mk a)) (s.obj (.mk b))).f k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S k hk) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt (s.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor.dgStandardEnrichedFunctor Q)) hab S k hk := by
  subst hk
  exact dgCoherentCubeComponent_naturality Q s hab S

lemma dgCoherentSimplex_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := D)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s).map Q = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex (s.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor.dgStandardEnrichedFunctor Q)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A E
  · intro a
    rfl
  · intro I a b k hI ha hb hk
    apply heq_of_eq
    change (Q.map _ _).f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).hom I a b k hI ha hb hk) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData (s.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardEnrichedFunctor.dgStandardEnrichedFunctor Q))).hom I a b k hI ha hb hk
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData]
    apply dgCoherentCubeComponentAt_naturality
end SerrePositivity.InfinityCategories.Project.DerivedCategories
