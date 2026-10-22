module
public import SerrePositivity.KST.SConstruction.PerfectVerdierDiagram
public import SerrePositivity.KST.LocalizingInvariants.VerdierPresentation

/-! # 元の冪等完備化後の射を保つ Verdier 四角形
概要：実商と完備化の合成を右辺とし、元の包含と零角を保つ coherent 四角形を作る。
方針：全対象の零化から関手同型を作り、StableInfinity の実際の四角形へ実現する。
規約：右端を未完備な商へ戻さない。使われ方：同じ四角形の Cat^perf への持ち上げ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open F2.Idempotent
open scoped Simplicial

/-- 実際の零安定圏は、全 coherent 冪等図式の強い分裂を持つ。 -/
lemma perfectZeroCategory_isIdempotentComplete : IsIdempotentComplete zeroCategory.{u}.obj := by
  let : ∀ n : SimplexCategoryᵒᵖ, Unique (zeroCategory.{u}.obj.obj n) :=
    fun _ => inferInstanceAs (Unique PUnit)
  intro d
  exact ⟨UniqueTarget.map _, UniqueTarget.hom_ext _ _⟩

/-- 元の二射と零角を経由する二射を全て固定した、実際の安定圏値四角形。 -/
lemma exists_perfectVerdierRawSquare (d : PerfectVerdierSequence.{u}) :
    ∃ Q : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u},
      squareBottomEdge ≫ Q = SSet.yonedaEquiv.symm (stableArrow d.verdier.inclusion).edge ∧
      squareTopEdge ≫ Q = SSet.yonedaEquiv.symm (stableArrow (fromZeroCategory d.right)).edge ∧
      squareLeftEdge ≫ Q =
        SSet.yonedaEquiv.symm (stableArrow (toZeroCategory d.verdier.left)).edge ∧
      squareRightEdge ≫ Q = SSet.yonedaEquiv.symm (stableArrow d.projection).edge := by
  apply exists_stableSquare_of_homMk_comm (stableArrow d.verdier.inclusion).toTruncated
    (stableArrow (fromZeroCategory d.right)).toTruncated
    (stableArrow (toZeroCategory d.verdier.left)).toTruncated (stableArrow d.projection).toTruncated
  have hi := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (C := StableQCat.{u}) d.verdier.inclusion d.projection).toTruncated
  have hz := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveCompStruct (C := StableQCat.{u})
      (toZeroCategory d.verdier.left) (fromZeroCategory d.right)).toTruncated
  let F : ExactMap d.verdier.left d.right :=
    ⟨d.verdier.inclusion.hom ≫ d.projection.hom, isExactFunctor_comp _ _⟩
  let G : ExactMap d.verdier.left d.right :=
    ⟨(toZeroCategory d.verdier.left).hom ≫ (fromZeroCategory d.right).hom,
      isExactFunctor_comp _ _⟩
  have he : FunctorIso F.hom G.hom :=
    zeroDiagramFunctorIso _ _ d.projection_kills_inclusion (fun k => by
      change IsZeroVertex (((toZeroCategory d.verdier.left).hom ≫
        (fromZeroCategory d.right).hom).app (Opposite.op ⦋0⦌) k)
      rw [throughZero_hom, zeroDiagram_const_vertex]
      exact (chosenZeroVertex d.right.obj).isZero)
  exact hi.trans ((stableArrow_homMk_eq_of_functorIso (F := F) (G := G) he).trans hz.symm)

/-- 選択した実四角形は、元の完備化後の右射を保持する。 -/
def perfectVerdierRawSquare (d : PerfectVerdierSequence.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u} :=
  Classical.choose (exists_perfectVerdierRawSquare d)

/-- 同じ選択した四角形の四辺は、元の四つの完全関手の辺そのもの。 -/
lemma perfectVerdierRawSquare_edges (d : PerfectVerdierSequence.{u}) :
    squareBottomEdge ≫ perfectVerdierRawSquare d =
        SSet.yonedaEquiv.symm (stableArrow d.verdier.inclusion).edge ∧
      squareTopEdge ≫ perfectVerdierRawSquare d =
        SSet.yonedaEquiv.symm (stableArrow (fromZeroCategory d.right)).edge ∧
      squareLeftEdge ≫ perfectVerdierRawSquare d =
        SSet.yonedaEquiv.symm (stableArrow (toZeroCategory d.verdier.left)).edge ∧
      squareRightEdge ≫ perfectVerdierRawSquare d =
        SSet.yonedaEquiv.symm (stableArrow d.projection).edge :=
  Classical.choose_spec (exists_perfectVerdierRawSquare d)

end SerrePositivity.KST.SConstruction
