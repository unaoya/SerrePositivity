module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ObjectLift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.RepresentableHomCoslice
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantCosliceTransport

/-!
概要：元の豊穣表現可能関手の coherent 実現を、正本の共変 Hom 全図式へ比較する。
方針：同じ恒等点からの coslice 全空間同値を分類し、対象宇宙の持ち上げを戻す。
規約：点ごとの値同値は全図式同型の根拠に用いない。
使われ方：HTT 5.1.3、E2-S (7) への Ind-S (8) の供給。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]

/-- 全 coherent 単体で、元の豊穣 Hom 関手をそのまま後合成する。 -/
lemma representableHomCoherent_app (x : D) (n : SimplexCategoryᵒᵖ)
    (s : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialNerve D)).obj n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x).app n s = s.down.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x) := rfl

/-- 零単体の値も、同じ元の Kan Hom の頂点。 -/
lemma representableHomCoherent_vertex (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x).obj y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallKanRealization_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x) y).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _).symm

/-- 対象宇宙の持ち上げは、元の豊穣 Hom 関手の全作用を保つ。 -/
lemma representableHomFunctor_objectLift (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.lower D).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor (D := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift D) (ULift.up x) := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro i j
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.lower, Category.id_comp,
    eqToHom_refl, Category.comp_id]

/-- 元の豊穣 Hom の全 coherent 実現と、指定された共変 Hom 全図式との同型。 -/
def representableHomCoherentIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) := by
  let x' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift D := ULift.up x
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomFunctor x'
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F
  have hg : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.nerveIso D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x = G := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.realization,
      representableHomFunctor_objectLift]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.covariantHomIsoOfDisplayedCosliceEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.nerveIso D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representableHomCoherent x) G hg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x') (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CoherentObjectLift.nerveIso_vertex D x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanCosliceComparison.map F x' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentityCoefficient x'))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanCosliceComparison.projection F x' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomIdentityCoefficient x'))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.representableHomCosliceComparison_isQCatEquivalence x').isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
