module

public import SerrePositivity.InfinityCategories.F1.Coherent.ObjectLift
public import SerrePositivity.InfinityCategories.F1.Coherent.RepresentableHomCoslice
public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantCosliceTransport

/-!
概要：元の豊穣表現可能関手の coherent 実現を、正本の共変 Hom 全図式へ比較する。
方針：同じ恒等点からの coslice 全空間同値を分類し、対象宇宙の持ち上げを戻す。
規約：点ごとの値同値は全図式同型の根拠に用いない。
使われ方：HTT 5.1.3、E2-S (7) への Ind-S (8) の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]

/-- 全 coherent 単体で、元の豊穣 Hom 関手をそのまま後合成する。 -/
lemma representableHomCoherent_app (x : D) (n : SimplexCategoryᵒᵖ)
    (s : ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialNerve D)).obj n) :
    (representableHomCoherent x).app n s = s.down.comp SSet (representableHomFunctor x) := rfl

/-- 零単体の値も、同じ元の Kan Hom の頂点。 -/
lemma representableHomCoherent_vertex (x y : D) :
    (representableHomCoherent x).app (Opposite.op ⦋0⦌) (ULift.up (coherentNerveVertex y)) =
      spaceInfinityVertex ((representableHomFunctor x).obj y) :=
  (smallKanRealization_vertex (representableHomFunctor x) y).trans
    (spaceInfinityVertex_eq_coherent _).symm

/-- 対象宇宙の持ち上げは、元の豊穣 Hom 関手の全作用を保つ。 -/
lemma representableHomFunctor_objectLift (x : D) :
    (CoherentObjectLift.lower D).comp SSet (representableHomFunctor x) =
      representableHomFunctor (D := CoherentObjectLift D) (ULift.up x) := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro i j
  simp only [EnrichedFunctor.comp_map, CoherentObjectLift.lower, Category.id_comp,
    eqToHom_refl, Category.comp_id]

/-- 元の豊穣 Hom の全 coherent 実現と、指定された共変 Hom 全図式との同型。 -/
def representableHomCoherentIso (x : D) :
    FunctorIso (representableHomCoherent x) (homInfinityCovariant (coherentNerveVertex x)) := by
  let x' : CoherentObjectLift D := ULift.up x
  let F := representableHomFunctor x'
  let G := coherentNerveMap F
  have hg : (CoherentObjectLift.nerveIso D).hom ≫ representableHomCoherent x = G := by
    rw [representableHomCoherent, CoherentObjectLift.realization,
      representableHomFunctor_objectLift]
  exact covariantHomIsoOfDisplayedCosliceEquivalence (CoherentObjectLift.nerveIso D)
    (representableHomCoherent x) G hg (coherentNerveVertex x') (coherentNerveVertex x)
    (CoherentObjectLift.nerveIso_vertex D x)
    (KanCosliceComparison.map F x' (representableHomIdentityCoefficient x'))
    (KanCosliceComparison.projection F x' (representableHomIdentityCoefficient x'))
    (representableHomCosliceComparison_isQCatEquivalence x').isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
