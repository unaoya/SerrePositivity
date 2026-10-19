module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceInitialCoordinates

/-!
概要：coherent nerve の coslice 全体に、反転した豊穣 Hom の全パラメータで前合成する。
方針：固定初点の simplex の初点を取り替え、join の同型で coslice へ戻す。
規約：局所 Kan 性や錐の極限性は不要。元の射影を厳密に保つ。
使われ方：HTT 4.2.4.1 の構成済みの錐の図式全体上の Hom の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- coslice の単体に豊穣 Hom の同じ次数のパラメータを前合成する。 -/
def cosliceSourcePrecompositionSimplex (x z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))) _⦋n⦌ := by
  refine ⟨(leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
    (coneInitialFixedSimplex x (cosliceInitialCoordinates z s) (SSet.yonedaEquiv.symm a)), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, coneInitialFixedSimplex_apex]

/-- coslice の前合成の単体は全ての面・退化で同時に制限できる。 -/
lemma cosliceSourcePrecompositionSimplex_naturality (x z : C) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))).map α.op
        (cosliceSourcePrecompositionSimplex x z s a) =
      cosliceSourcePrecompositionSimplex x z
        ((sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))).map α.op s)
        ((SimplicialCategory.sHom x z).op.map α.op a) := by
  apply Subtype.ext
  change joinMap (𝟙 Δ[0]) (stdSimplex.map α) ≫
      ((pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (coneInitialFixedSimplex x (cosliceInitialCoordinates z s) (SSet.yonedaEquiv.symm a))) =
    (pointJoinStdSimplexIso m).hom ≫ SSet.yonedaEquiv.symm _
  rw [← Category.assoc, joinStdSimplexIso_point_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  have hy : SSet.yonedaEquiv.symm ((SimplicialCategory.sHom x z).op.map α.op a) =
      stdSimplex.map α ≫ SSet.yonedaEquiv.symm a :=
    (SSet.yonedaEquiv_symm_naturality_left α a).symm
  rw [hy, cosliceInitialCoordinates_reindex]
  congr 1
  exact congrArg SSet.yonedaEquiv.symm
    (coneInitialFixedSimplex_reindex x α (cosliceInitialCoordinates z s)
      (SSet.yonedaEquiv.symm a))

/-- 各単体で coslice の前合成は元の射影の値を保つ。 -/
lemma cosliceSourcePrecompositionSimplex_projection (x z : C) {n : ℕ}
    (s : (sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z))) _⦋n⦌)
    (a : (SimplicialCategory.sHom x z).op _⦋n⦌) :
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))).app
        (Opposite.op ⦋n⦌) (cosliceSourcePrecompositionSimplex x z s a) =
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z))).app
        (Opposite.op ⦋n⦌) s := by
  change SSet.yonedaEquiv (joinInr Δ[0] Δ[n] ≫
    ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm _)) = _
  rw [← Category.assoc, joinStdSimplexIso_leftPoint_inr,
    stdSimplex.δ_comp_yonedaEquiv_symm, coneInitialFixedSimplex_tail, Equiv.apply_symm_apply]
  exact coherentCosliceSourceSimplex_tail z s

/-- coslice 全体に対する反転した Hom の全パラメータの前合成の射。 -/
def coherentCosliceSourcePrecomposition (x z : C) :
    sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z)) ⊗
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) where
  app _ := ↾fun ⟨s, a⟩ ↦ cosliceSourcePrecompositionSimplex x z s a.down
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨s, a⟩
    exact (cosliceSourcePrecompositionSimplex_naturality x z α.unop s a.down).symm

/-- coslice の前合成の射は、全 Hom パラメータで元の射影を保つ。 -/
lemma coherentCosliceSourcePrecomposition_over (x z : C) :
    coherentCosliceSourcePrecomposition x z ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
      fst _ _ ≫ sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  exact cosliceSourcePrecompositionSimplex_projection x z s a.down

end
end SerrePositivity.InfinityCategories.HomotopyLimits
