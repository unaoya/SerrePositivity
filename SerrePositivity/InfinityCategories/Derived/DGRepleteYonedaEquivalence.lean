module
public import SerrePositivity.InfinityCategories.Derived.DGRepleteYoneda
public import SerrePositivity.InfinityCategories.Derived.DGVertexIsoOfH0
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-! # ホモトピー表現可能部分との明示的 ∞ 圏同値

概要：対象宇宙を上げた任意の dg 圏の nerve はホモトピー表現可能部分と同値。
方針：H⁰ 包含の完全忠実性で代表加群との同型を反映し、Core の実頂点同型へ送る。
規約：前三角性は不要。使われ方：前三角 dg 圏の安定性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ホモトピー表現可能な対象は、内部でも代表加群の頂点と実同型になる。 -/
lemma dgRepleteRepresentable_vertex_iso (M : DGRepleteRepresentables A D) :
    ∃ x : D, Nonempty (VertexIso (X := dgNerve A (DGRepleteRepresentables A D))
      (Simplex.vertex ((dgRepleteYoneda A D).obj ⟨ULift.up x⟩)) (Simplex.vertex M)) := by
  obtain ⟨x, ⟨e⟩⟩ := (dgRepresentableHomotopyProperty_iff A D _).1 M.property
  let R : DGRepleteRepresentables A D :=
    ⟨representable A x, dgHomotopyRepresentable_representable A D x⟩
  let F := dgFullSubcategoryInclusion A (RightModule A D) (dgHomotopyRepresentable A D)
  let e' : (toHomotopy A (DGRepleteRepresentables A D)).obj
      (ForgetEnrichment.of (Complex A) M) ≅
      (toHomotopy A (DGRepleteRepresentables A D)).obj
        (ForgetEnrichment.of (Complex A) R) := F.onHomotopy.preimageIso e
  exact ⟨x, ⟨dgVertexIsoOfH0 A (DGRepleteRepresentables A D) e'.symm⟩⟩

/-- 実 dg Yoneda の nerve はホモトピー表現可能部分の全対象を同値まで覆う。 -/
lemma dgRepleteYonedaNerve_isEssentiallySurjective :
    IsEssentiallySurjective (dgNerve.map (dgRepleteYoneda A D)) := by
  intro y
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  obtain ⟨x, e⟩ := dgRepleteRepresentable_vertex_iso A D M
  refine ⟨Simplex.vertex (⟨ULift.up x⟩ : DGUniverseLift.{v, max (u + 1) v} D), ?_⟩
  rw [dgFunctorNerve_vertex]
  exact e

/-- 共通宇宙の元の dg nerve とホモトピー表現可能部分の明示的 ∞ 圏同値。 -/
def dgRepleteYonedaNerveEquivalence :
    QCatEquivalence (dgNerve A (DGUniverseLift.{v, max (u + 1) v} D))
      (dgHomotopyRepresentableNerve A D) :=
  qCatEquivalenceOfFullyFaithfulEssentiallySurjective (dgNerve.map (dgRepleteYoneda A D))
    (dgRepleteYonedaNerve_isFullyFaithful A D) (dgRepleteYonedaNerve_isEssentiallySurjective A D)

/-- 明示的同値の順方向は実 dg Yoneda の nerve そのもの。 -/
lemma dgRepleteYonedaNerveEquivalence_hom :
    (dgRepleteYonedaNerveEquivalence A D).hom = dgNerve.map (dgRepleteYoneda A D) := rfl

end SerrePositivity.InfinityCategories
