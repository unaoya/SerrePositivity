module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDeformationEnriched

/-!
概要：三角形の始点だけを時刻零に残す path 変形。
方針：時刻一の点の後ろには新たな中間頂点がないことを使う。
規約：元の path とその包含を厳密に保持する。
使われ方：指定精密化を保持する合成比較三単体の元の面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三角形の時刻 (0,1,1)。 -/
def coherentTriangleDeformationTime : ULift.{u} (Fin 3) →o Fin 2 :=
  (SimplexCategory.σ (1 : Fin 2)).toOrderHom.comp ⟨ULift.down, fun _ _ h ↦ h⟩

/-- この時刻で恒等対象写像を変形しても三角形の path は変わらない。 -/
lemma coherentTriangleDeformationTime_path
    {i j : ULift.{u} (Fin 3)} (P : Path i j) :
    coherentPathDeformation (OrderHom.id) coherentTriangleDeformationTime P = P := by
  apply SimplicialThickening.Path.ext
  ext z
  change (z ∈ OrderHom.id '' P.I ∨
    ∃ k ∈ P.I, coherentTriangleDeformationTime k = 1 ∧ k ≤ z ∧ z ≤ j) ↔ z ∈ P.I
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, ht, hkz, hzj⟩)
    · exact hk
    · have hkj := P.le_right k hk
      have hkn : k.down ≠ 0 := by
        rintro h
        have he : k = ULift.up (0 : Fin 3) := ULift.ext h
        subst k
        change (0 : Fin 2) = 1 at ht
        exact (by decide : (0 : Fin 2) ≠ 1) ht
      have hz : z = k ∨ z = j := by
        have hklt := k.down.isLt
        have hjlt := j.down.isLt
        have hzlt := z.down.isLt
        change k.down ≤ z.down at hkz
        change z.down ≤ j.down at hzj
        have h : z.down = k.down ∨ z.down = j.down := by omega
        exact h.elim (fun h ↦ Or.inl (ULift.ext h))
          (fun h ↦ Or.inr (ULift.ext h))
      rcases hz with rfl | rfl
      · exact hk
      · exact P.right
  · intro hz
    exact Or.inl ⟨z, hz, rfl⟩

/-- 元の三角形の全 Hom の nerve を保持する豊穣関手の等式。 -/
lemma coherentTriangleDeformationTime_enriched :
    coherentPathDeformationEnriched (OrderHom.id (α := ULift.{u} (Fin 3)))
      coherentTriangleDeformationTime = EnrichedFunctor.id SSet _ := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun z ↦ coherentTriangleDeformationTime_path (P.obj z))

end SerrePositivity.InfinityCategories.F2
