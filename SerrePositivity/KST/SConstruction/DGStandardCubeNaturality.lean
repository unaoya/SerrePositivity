module
public import SerrePositivity.KST.SConstruction.DGStandardEnrichedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComponentDegree

/-! # 標準 DK 立方体評価の厳密 dg 後合成自然性
概要：元の最大旗の符号付き和と、元の dg 関手の全次数 Hom 作用の可換性を示す。
方針：各旗の最上位成分を同じ Hom 鎖射で写し、有限和と整数係数を保つ。
規約：元の全旗と降順の向きを保持。使われ方：既存 DK 比較と native dg 作用の照合。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 元の標準 DK 単体の最上位評価は、元の dg Hom 鎖射と可換。 -/
lemma dgStandardTopEval_post (F : DGFunctor A D E) {x y : D} {m : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := A) (F.obj x) (F.obj y) m (dgStandardSimplexMap F s) =
      (F.map x y).f (-(m : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := A) x y m s) := rfl

/-- 元の各最大旗の評価は、元の dg Hom 鎖射と可換。 -/
lemma dgStandardCubeFlag_post (F : DGFunctor A D E) {x y : D} {T : Type u} {m : ℕ}
    (e : Fin m ≃ T) (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e (φ ≫ dgStandardHomMap F x y) =
      (F.map x y).f (-(m : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation e φ) := rfl

/-- 元の全最大旗の符号付き和の評価は、元の dg Hom 鎖射と可換。 -/
lemma dgStandardCubeEvaluation_post (F : DGFunctor A D E) {x y : D} {T : Type u} {m : ℕ}
    (e : Fin m ≃ T) (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (φ ≫ dgStandardHomMap F x y) =
      (F.map x y).f (-(m : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e φ) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  simp only [map_sum, map_zsmul, dgStandardCubeFlag_post]

/-- coherent 単体の元の立方体 Hom 制限は、標準 DK 豊穣後合成と可換。 -/
lemma dgStandardCoherentCubeHom_post (F : DGFunctor A D E) {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (CategoryTheory.SimplicialThickening J) (ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom (s.comp SSet (dgStandardEnrichedFunctor F)) hab S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S ≫ dgStandardHomMap F (s.obj (.mk a)) (s.obj (.mk b)) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

/-- coherent 単体の元の全内部点成分は、標準 DK 豊穣後合成と可換。 -/
lemma dgStandardCoherentCubeComponent_post (F : DGFunctor A D E) {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (CategoryTheory.SimplicialThickening J) (ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent (s.comp SSet (dgStandardEnrichedFunctor F)) hab S =
      (F.map (s.obj (.mk a)) (s.obj (.mk b))).f (-(S.card : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent s hab S) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent
  rw [dgStandardCoherentCubeHom_post]
  exact dgStandardCubeEvaluation_post F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration S) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S)

/-- 同じ次数を指定した全内部点成分も、元の dg Hom 鎖射と可換。 -/
lemma dgStandardCoherentCubeComponentAt_post (F : DGFunctor A D E) {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (CategoryTheory.SimplicialThickening J) (ClosedCategory A D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) (k : ℤ) (hk : k = -(S.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt (s.comp SSet (dgStandardEnrichedFunctor F)) hab S k hk =
      (F.map (s.obj (.mk a)) (s.obj (.mk b))).f k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S k hk) := by
  subst hk
  exact dgStandardCoherentCubeComponent_post F s hab S

end SerrePositivity.KST.SConstruction
