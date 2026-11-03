module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedron

/-!
概要：合成比較三単体の最後の面には path の追加が生じない。
方針：対象写像の像 (0,0,1) の全区間に中間の頂点がないことを使う。
規約：任意の path と元の包含を保持する。
使われ方：最後の面を元の最初の辺の退化に同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後の面の対象写像 (0,0,1)。 -/
def coherentCompositionTetrahedronLastObjects : ULift.{u} (Fin 3) →o ULift.{u} (Fin 3) :=
  coherentCompositionTetrahedronObjects.comp
    (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap

/-- 最後の面の対象写像の値は 0 または 1。 -/
lemma coherentCompositionTetrahedronLastObjects_bound (i : ULift.{u} (Fin 3)) :
    (coherentCompositionTetrahedronLastObjects i).down.val ≤ 1 := by
  rcases i with ⟨i⟩
  fin_cases i <;> decide

/-- 最後の面では任意の時刻でも元の path の像のまま。 -/
lemma coherentCompositionTetrahedronLastObjects_path
    (t : ULift.{u} (Fin 3) →o Fin 2) {i j : ULift.{u} (Fin 3)} (P : Path i j) :
    coherentPathDeformation coherentCompositionTetrahedronLastObjects t P =
      (SimplicialThickening.functorMap coherentCompositionTetrahedronLastObjects
        ⟨i⟩ ⟨j⟩).obj P := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ coherentCompositionTetrahedronLastObjects '' P.I ∨
    ∃ k ∈ P.I, t k = 1 ∧ coherentCompositionTetrahedronLastObjects k ≤ z ∧
      z ≤ coherentCompositionTetrahedronLastObjects j) ↔
        z ∈ coherentCompositionTetrahedronLastObjects '' P.I
  constructor
  · rintro (hz | ⟨k, hk, _, hkz, hzj⟩)
    · exact hz
    · have hj1 := coherentCompositionTetrahedronLastObjects_bound j
      have hkz' : (coherentCompositionTetrahedronLastObjects k).down.val ≤
          z.down.val := hkz
      have hzj' : z.down.val ≤
          (coherentCompositionTetrahedronLastObjects j).down.val := hzj
      have hz : z = coherentCompositionTetrahedronLastObjects k ∨
          z = coherentCompositionTetrahedronLastObjects j := by
        have h : z.down.val = (coherentCompositionTetrahedronLastObjects k).down.val ∨
            z.down.val = (coherentCompositionTetrahedronLastObjects j).down.val := by omega
        exact h.elim (fun h ↦ Or.inl (ULift.ext (Fin.ext h)))
          (fun h ↦ Or.inr (ULift.ext (Fin.ext h)))
      rcases hz with rfl | rfl
      · exact ⟨k, hk, rfl⟩
      · exact ⟨j, P.right, rfl⟩
  · exact Or.inl

/-- 最後の面の変形豊穣関手は通常の対象写像の豊穣表示。 -/
lemma coherentCompositionTetrahedronLastObjects_enriched
    (t : ULift.{u} (Fin 3) →o Fin 2) :
    coherentPathDeformationEnriched coherentCompositionTetrahedronLastObjects t =
      SimplicialThickening.functor coherentCompositionTetrahedronLastObjects := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentCompositionTetrahedronLastObjects_path t (P.obj z))

end SerrePositivity.InfinityCategories.F2
