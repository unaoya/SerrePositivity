module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift

/-! # 元の dg 二セルの共通宇宙への移送
概要：独立宇宙の dg 単体の関手像は、合成・面と可換である。
方針：元の SimplexData の全成分の等式を実単体へ持ち上げる。
規約：対象を上げ下げしても元の像を厳密に回収。使われ方：二軸 cofiber の貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D] {E : Type z} [DGCategory R E]

/-- 元の単体の二回の実関手像は、同じ合成関手の像。 -/
lemma dgSimplex_map_comp {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (F : DGFunctor R C D) (H : DGFunctor R D E) : (s.map F).map H = s.map (F.comp H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp s.toSimplexData F H).symm

/-- 元の単体の実関手像の面は、同じ元の面の像。 -/
lemma dgSimplex_map_face {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C (n + 1))
    (F : DGFunctor R C D) (i : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D).δ i (s.map F) = ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ i s).map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback s.toSimplexData F (SimplexCategory.δ i).toOrderHom).symm

/-- 対象宇宙を上げてから下げた元の単体の像は、元の関手像を厳密に回収する。 -/
lemma dgSimplex_commonUniverse_map {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (F : DGFunctor R C D) :
    (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, t} R C)).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R C).comp F) = s.map F := by
  rw [dgSimplex_map_comp, ← strictDGFunctor_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down,
    strictDGFunctor_id_comp]

end SerrePositivity.KST.SConstruction
