module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableObjectProperty
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseZeroObjects
/-!
概要：零化される dg 対象条件の充満包含の本質像は、実関手の零対象核と一致する。
方針：実頂点のラベルを使って核内対象を選び、頂点同型による零性の移送を行う。
規約：任意の追加 ULift 宇宙を許し、商や局所化の普遍性は仮定しない。
使われ方：D-16 の thick 核包含と Sp の kernel 欄の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (P : D → Prop) {Y : SSet.{max u v}} [Quasicategory Y]
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D ⟶ Y)
  (hP : ∀ x, P x ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
include hP

lemma dgFullKernel_zero_iff_essentialImage (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P)) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P)).app (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro h
    have hb : P (b.obj 0) := (hP _).mpr (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj]; exact h)
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.obj 0, hb⟩ : DGFullSubcategory D P), ?_⟩
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
    change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (b.obj 0)) b)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_vertex_obj]
    exact ⟨Iso.refl _⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective a
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) b at e
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e
    exact ((hP x.val).mp x.property).of_vertexIso (e.map F)

lemma dgFullKernel_ulift_zero_iff_essentialImage
    (b : ((SSet.uliftFunctor.{w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((SSet.uliftFunctor.{w}).map F).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory D P))) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (((SSet.uliftFunctor.{w}).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro h
    have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) b.down) :=
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mpr h
    obtain ⟨a, ⟨e⟩⟩ := (dgFullKernel_zero_iff_essentialImage R D P F hP b.down).mp hz
    exact ⟨ULift.up a, ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.uliftVertexIso e⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    have hz := (dgFullKernel_zero_iff_essentialImage R D P F hP b.down).mpr
      ⟨a.down, ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso e⟩⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _).mp hz

end SerrePositivity.InfinityCategories.Project.DerivedCategories
