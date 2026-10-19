module
public import SerrePositivity.InfinityCategories.Derived.DGYonedaFiniteCellClosure
public import SerrePositivity.InfinityCategories.Derived.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexClosure

/-! # 元の native dg nerve の実閉包と有限 cell

概要：元の宇宙の dg nerve の実安定閉包は代表加群の有限 cell 条件で判定できる。
方針：実閉包の ULift 不変性と、対象持ち上げの nerve の実同型で共通宇宙の比較を降下する。
規約：対象宇宙の持ち上げを結論に残さない。使われ方：有限 cell roof の native 分母条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 持ち上げた指定頂点の nerve の実同型による像は、対象を持ち上げた指定頂点と一致。 -/
lemma dgLiftedGeneratorVertices_universe_image (P : Set D) :
    (dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D).hom.app (Opposite.op ⦋0⦌) ''
      (ULift.up '' (Simplex.vertex '' P)) = dgLiftedGeneratorVertices A D P := by
  change _ '' (ULift.up '' (Simplex.vertex '' P)) =
    Simplex.vertex '' ((dgUniverseLiftUp A D).obj '' P)
  rw [Set.image_image, Set.image_image, Set.image_image]
  apply congrArg (fun f : D →
    (dgNerve A (DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌ => f '' P)
  funext x
  apply Simplex.vertexEquiv.injective
  rfl

variable [IsDGPretriangulated A D]

/-- 元の native dg nerve の実閉包と、代表加群の有限 cell 条件の一致。 -/
theorem dgNative_stableVertexClosure_iff_finiteCell (P : Set D) (x : D) :
    StableVertexClosure (X := dgNerve A D) (Simplex.vertex '' P) (Simplex.vertex x) ↔
      homotopyFiniteCellOver A D P ((moduleToHomotopy A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x))) := by
  let := dgNerveULift_isStable_of_pretriangulated A D
  let := dgUniverseLiftNerve_isStable A D
  let e := dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D
  let : IsExactFunctor e.hom :=
    isExactFunctor_of_isQCatEquivalence (qCatEquivalenceOfIso e).isQCatEquivalence
  have h := stableVertexClosure_image_iff e.hom
    (qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful
    (ULift.up '' (Simplex.vertex '' P)) (ULift.up (Simplex.vertex x))
  have hv : e.hom.app (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex x)) =
      Simplex.vertex ((dgUniverseLiftUp A D).obj x) := by
    apply Simplex.vertexEquiv.injective
    rfl
  rw [dgLiftedGeneratorVertices_universe_image, hv] at h
  exact (stableVertexClosure_ulift_iff.{max u v, max (u + 1) v}
    (X := dgNerve A D) (Simplex.vertex '' P) (Simplex.vertex x)).symm.trans
      (h.symm.trans (dgLifted_stableVertexClosure_iff_finiteCell A D P x))

/-- 任意の実 cofiber 頂点を元の dg 対象で表示すると、分母条件を有限 cell で判定できる。 -/
theorem dgVerdierEdges_mem_iff_finiteCell (P : Set D) {a : (dgNerve A D) _⦋1⦌}
    (s : CofiberSquare (edgeOfSimplex a)) (z : D)
    (hz : s.cofiber = Simplex.vertex z) :
    a ∈ dgVerdierEdges A D P ↔ homotopyFiniteCellOver A D P
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) := by
  rw [dgVerdierEdges_mem_iff A D P s, hz]
  exact dgNative_stableVertexClosure_iff_finiteCell A D P z

end SerrePositivity.InfinityCategories
