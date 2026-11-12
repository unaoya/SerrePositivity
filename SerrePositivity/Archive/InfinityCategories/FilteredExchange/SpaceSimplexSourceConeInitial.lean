module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexSourceCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourceIdentity

/-!
概要：元の初点からの coslice 単体を初点へ制限すると、元の恒等射を回収する。
方針：初点を重ねた順序写像を定値写像へ戻し、恒等 coslice 点の座標と比較する。
規約：元の全 Hom 族への入力を保持。使われ方：pointed 族の始点の標準比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)

/-- 初点へ制限した元の coslice の座標は、同じ初点の恒等辺。 -/
lemma spaceSimplexSourceCone_initial_coordinates :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩)
      ((sliceUnder (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).map
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op (spaceSimplexSourceCone s)) =
      PinchedHom.constant (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) 1 := by
  let α := SimplexCategory.const ⦋0⦌ ⦋n⦌ 0
  refine (coherentCosliceSourceSimplex_reindex _ α (spaceSimplexSourceCone s)).symm.trans ?_
  change SpaceInfinity.map (SimplexCategory.mkHom
    (prependOrderHom α.toOrderHom)).op
      (coherentCosliceSourceSimplex _ (spaceSimplexSourceCone s)) = _
  rw [spaceSimplexSourceCone_coordinates, coherentConeTailExtension_eq_sigmaZero]
  change SpaceInfinity.map (SimplexCategory.mkHom
    (prependOrderHom α.toOrderHom)).op
      (SpaceInfinity.map (SimplexCategory.σ 0).op s) = _
  rw [← Functor.map_comp_apply, ← op_comp]
  have h : SimplexCategory.mkHom (prependOrderHom α.toOrderHom) ≫ SimplexCategory.σ 0 =
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫ α := by
    ext j
    fin_cases j <;> rfl
  rw [h, op_comp, Functor.map_comp_apply]
  have hv : SpaceInfinity.map α.op s = coherentNerveVertex (s.obj ⟨ULift.up 0⟩) := by
    apply (coherentNerveVertexEquiv KanObject).symm.injective
    rfl
  rw [hv]
  rfl

/-- 元の coslice 族の初点は、同じ初点における元の恒等 coslice 点そのもの。 -/
lemma spaceSimplexSourceCone_initial :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
      SSet.yonedaEquiv.symm (spaceSimplexSourceCone s) =
        cosliceIdentityPoint (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  apply SSet.yonedaEquiv.injective
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso 0).inv).mp
  apply SSet.yonedaEquiv.injective
  have h := spaceSimplexSourceCone_initial_coordinates s
  have hi := congrArg Subtype.val
    (cosliceInitialCoordinates_identity (s.obj ⟨ULift.up 0⟩)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}))))
  change coherentCosliceSourceSimplex _
    (SSet.yonedaEquiv (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
      SSet.yonedaEquiv.symm (spaceSimplexSourceCone s))) =
    coherentCosliceSourceSimplex _
      (SSet.yonedaEquiv (cosliceIdentityPoint (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))))
  erw [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact h.trans hi.symm

/-- 初点の零単体での値も、同じ元の恒等 coslice 点の零単体に厳密に等しい。 -/
lemma spaceSimplexSourceCone_initial_vertex :
    (SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) =
        SSet.yonedaEquiv (cosliceIdentityPoint
          (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))) := by
  have h := congrArg SSet.yonedaEquiv (spaceSimplexSourceCone_initial s)
  erw [SSet.yonedaEquiv_comp] at h
  exact h

end SerrePositivity.InfinityCategories.F2
