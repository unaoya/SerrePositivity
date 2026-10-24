module
public import SerrePositivity.InfinityCategories.Derived.DGStandardEnrichedFunctor
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentComparison
public import SerrePositivity.InfinityCategories.Derived.DGSimplexComponentExt
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded DGNerve DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

lemma dgCoherentCubeComponent_naturality (Q : DGFunctor A D E)
    {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    (Q.map (s.obj (.mk a)) (s.obj (.mk b))).f (-(S.card : ℤ))
      (coherentCubeComponent s hab S) =
      coherentCubeComponent (s.comp SSet (dgStandardEnrichedFunctor Q)) hab S := by
  unfold coherentCubeComponent cubeEvaluation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul]
  apply congrArg ((Equiv.Perm.sign σ : ℤ) • ·)
  exact (dgStandardSimplexMap_component (Q.map _ _)
    ((coherentCubeHom s hab S).app _ (cubeFlag (σ.trans (descendingEnumeration S))))
    Finset.univ (-(S.card : ℤ)) Finset.univ_nonempty (by simp)).symm

lemma dgCoherentCubeComponentAt_naturality (Q : DGFunctor A D E)
    {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) (k : ℤ) (hk : k = -(S.card : ℤ)) :
    (Q.map (s.obj (.mk a)) (s.obj (.mk b))).f k
      (coherentCubeComponentAt s hab S k hk) =
      coherentCubeComponentAt (s.comp SSet (dgStandardEnrichedFunctor Q)) hab S k hk := by
  subst hk
  exact dgCoherentCubeComponent_naturality Q s hab S

lemma dgCoherentSimplex_naturality (Q : DGFunctor A D E) {n : ℕ}
    (s : (doldKanCoherentNerve (R := A) (D := D)) _⦋n⦌) :
    (coherentSimplex s).map Q = coherentSimplex (s.comp SSet (dgStandardEnrichedFunctor Q)) := by
  apply Simplex.ext
  apply dgSimplexData_ext_of_components A E
  · intro a
    rfl
  · intro I a b k hI ha hb hk
    apply heq_of_eq
    change (Q.map _ _).f k ((coherentSimplexData s).hom I a b k hI ha hb hk) =
      (coherentSimplexData (s.comp SSet (dgStandardEnrichedFunctor Q))).hom I a b k hI ha hb hk
    dsimp only [coherentSimplexData]
    apply dgCoherentCubeComponentAt_naturality
end SerrePositivity.InfinityCategories
