module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedAugmentation

/-!
概要：元の Space 単体を、同じ初点からの退化 coslice 単体へ持ち上げる。
方針：初点を重ねた既存の tail 拡張を join の標準同型で読む。
規約：元の全単体と初点を保持。使われ方：全 Hom 係数の coslice 前合成の入力。
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

/-- 元の単体の初点を重ねた、同じ全単体を tail に持つ coslice 単体。 -/
def spaceSimplexSourceCone :
    (sliceUnder (SSet.yonedaEquiv.symm
      (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))) _⦋n⦌ := by
  refine ⟨(leftPointStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm (coherentConeTailExtension s), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left]
  congr 1
  apply (coherentNerveVertexEquiv KanObject).symm.injective
  rfl

/-- 初点からの実 coslice の座標は、元の初点退化の全単体そのもの。 -/
lemma spaceSimplexSourceCone_coordinates :
    coherentCosliceSourceSimplex (s.obj ⟨ULift.up 0⟩) (spaceSimplexSourceCone s) =
      coherentConeTailExtension s := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (coherentConeTailExtension s))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 固定初点を含む座標も、同じ元の tail 拡張を保持する。 -/
lemma spaceSimplexSourceCone_initialCoordinates :
    cosliceInitialCoordinates (s.obj ⟨ULift.up 0⟩) (spaceSimplexSourceCone s) =
      (⟨coherentConeTailExtension s, rfl⟩ :
        fixedInitialSimplex (s.obj ⟨ULift.up 0⟩) n) := by
  apply Subtype.ext
  exact spaceSimplexSourceCone_coordinates s

/-- この coslice 単体の実射影は、元の全 Space 単体に厳密に等しい。 -/
lemma spaceSimplexSourceCone_projection :
    (sliceUnderProjection (SSet.yonedaEquiv.symm
      (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)))).app (Opposite.op ⦋n⦌)
        (spaceSimplexSourceCone s) = s :=
  (coherentCosliceSourceSimplex_tail _ _).symm.trans
    ((congrArg (fun t => SpaceInfinity.δ 0 t) (spaceSimplexSourceCone_coordinates s)).trans
      (coherentConeTailExtension_tail s))

/-- 元の全標準単体の射影も、同じ元の図式の Yoneda 射そのもの。 -/
lemma spaceSimplexSourceCone_map_projection :
    SSet.yonedaEquiv.symm (spaceSimplexSourceCone s) ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex (s.obj ⟨ULift.up 0⟩))) = SSet.yonedaEquiv.symm s := by
  exact (SSet.yonedaEquiv_symm_comp _ _).trans
    (congrArg SSet.yonedaEquiv.symm (spaceSimplexSourceCone_projection s))

end SerrePositivity.InfinityCategories.F2
