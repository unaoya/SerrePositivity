module
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Derived.DGStableObjectProperty
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Core.UniverseZeroObjects
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (P : D → Prop) {Y : SSet.{max u v}} [Quasicategory Y]
  (F : dgNerve R D ⟶ Y)
  (hP : ∀ x, P x ↔ IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)))
include hP

lemma dgFullKernel_zero_iff_essentialImage (b : (dgNerve R D) _⦋0⦌) :
    IsZeroVertex (F.app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (dgNerve R (DGFullSubcategory D P)) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (dgFullSubcategoryInclusion R D P)).app (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro h
    have hb : P (b.obj 0) := (hP _).mpr (by rw [dgNerve_vertex_obj]; exact h)
    refine ⟨Simplex.vertex (⟨b.obj 0, hb⟩ : DGFullSubcategory D P), ?_⟩
    rw [dgFunctorNerve_vertex]
    change Nonempty (VertexIso (Simplex.vertex (b.obj 0)) b)
    rw [dgNerve_vertex_obj]
    exact ⟨Iso.refl _⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    change VertexIso ((dgNerve.map (dgFullSubcategoryInclusion R D P)).app
      (Opposite.op ⦋0⦌) (Simplex.vertex x)) b at e
    rw [dgFunctorNerve_vertex] at e
    exact ((hP x.val).mp x.property).of_vertexIso (e.map F)

lemma dgFullKernel_ulift_zero_iff_essentialImage
    (b : ((SSet.uliftFunctor.{w}).obj (dgNerve R D)) _⦋0⦌) :
    IsZeroVertex (((SSet.uliftFunctor.{w}).map F).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{w}).obj
          (dgNerve R (DGFullSubcategory D P))) _⦋0⦌,
        Nonempty (VertexIso
          (((SSet.uliftFunctor.{w}).map
            (dgNerve.map (dgFullSubcategoryInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro h
    have hz : IsZeroVertex (F.app (Opposite.op ⦋0⦌) b.down) :=
      (isZeroVertex_iff_ulift _).mpr h
    obtain ⟨a, ⟨e⟩⟩ := (dgFullKernel_zero_iff_essentialImage R D P F hP b.down).mp hz
    exact ⟨ULift.up a, ⟨uliftVertexIso e⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    have hz := (dgFullKernel_zero_iff_essentialImage R D P F hP b.down).mpr
      ⟨a.down, ⟨downVertexIso e⟩⟩
    exact (isZeroVertex_iff_ulift _).mp hz

end SerrePositivity.InfinityCategories
