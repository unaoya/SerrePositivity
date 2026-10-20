module
public import SerrePositivity.InfinityCategories.Derived.DGStableSubcategory
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedStability
/-!
概要：指定対象の実安定閉包の包含と、完全関手による零化の同値。
方針：実安定閉包の帰納法と包含の実頂点の式を使う。
規約：全頂点について零化する。使われ方：指定対象の零化から Verdier 列への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 元の実安定閉包の包含。 -/
def dgStableClosureInclusion (P : Set D) : dgStableClosureNerve A D P ⟶ dgNerve A D :=
  dgNerve.map (dgFullSubcategoryInclusion A D (dgStableClosureProperty A D P))
/-- 指定対象の実安定閉包からなる nerve は安定。 -/
lemma dgStableClosureNerve_isStable (P : Set D) : IsStable (dgStableClosureNerve A D P) := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact dgStableSubcategory_isStable A D _ (dgStableClosureProperty_isStable A D P)
/-- 安定閉包の包含は完全。 -/
lemma dgStableClosureInclusion_isExactFunctor (P : Set D) :
    IsExactFunctor (dgStableClosureInclusion A D P) := by
  let := dgNerve_isStable_of_pretriangulated A D
  exact dgStableSubcategoryInclusion_isExactFunctor A D _
    (dgStableClosureProperty_isStable A D P)
omit [Small.{u} D] [IsDGPretriangulated A D] in
/-- 安定閉包の包含は全写像空間で充満忠実。 -/
lemma dgStableClosureInclusion_isFullyFaithful (P : Set D) :
    IsFullyFaithful (dgStableClosureInclusion A D P) :=
  dgFullSubcategoryInclusionNerve_isFullyFaithful A D _
/-- 完全関手が指定対象を零化すれば、安定閉包の包含との合成の全頂点を零化する。 -/
lemma dgStableClosureInclusion_kills {Y : SSet.{max u v}} [Quasicategory Y] [IsStable Y]
    (P : Set D) (F : dgNerve A D ⟶ Y) [IsExactFunctor F]
    (h : ∀ x ∈ P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)))
    (z : (dgStableClosureNerve A D P) _⦋0⦌) :
    IsZeroVertex ((dgStableClosureInclusion A D P ≫ F).app (Opposite.op ⦋0⦌) z) := by
  let := dgNerve_isStable_of_pretriangulated A D
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  change IsZeroVertex (F.app _ ((dgNerve.map _).app _ (Simplex.vertex x)))
  rw [dgFunctorNerve_vertex]
  exact kills_stableVertexClosure F (Simplex.vertex '' P)
    (by rintro _ ⟨a, ha, rfl⟩; exact h a ha) x.property
/-- 安定閉包全体の零化と、元の指定対象の零化は同値。 -/
lemma dgStableClosureInclusion_kills_iff {Y : SSet.{max u v}} [Quasicategory Y] [IsStable Y]
    (P : Set D) (F : dgNerve A D ⟶ Y) [IsExactFunctor F] :
    (∀ z, IsZeroVertex ((dgStableClosureInclusion A D P ≫ F).app (Opposite.op ⦋0⦌) z)) ↔
      ∀ x ∈ P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
  constructor
  · intro h x hx
    let a : DGFullSubcategory D (dgStableClosureProperty A D P) :=
      ⟨x, StableVertexClosure.of_mem ⟨x, hx, rfl⟩⟩
    have hz := h (Simplex.vertex a)
    change IsZeroVertex (F.app _ ((dgNerve.map _).app _ (Simplex.vertex a))) at hz
    rw [dgFunctorNerve_vertex] at hz
    exact hz
  · intro h
    exact dgStableClosureInclusion_kills A D P F h
end SerrePositivity.InfinityCategories
