module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.TerminalShapeColimit

/-!
概要：形状同型と終頂点を持つ形状について、元の関手の余極限保存を得る。
方針：両側の全余錐制限を用い、一点の恒等余錐とその同じ像へ帰着する。
規約：元の図式を保持し、関手の可逆性を要求しない。
使われ方：I-2 d′ の保存性の有限セル帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 形状の厳密な同型への制限は余極限保存の存在を変えない。 -/
lemma hasPreservedColimit_iff_restrict_isIso
    {A K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (p : K ⟶ X) (i : A ⟶ K) [IsIso i] :
    HasPreservedColimit U p ↔ HasPreservedColimit U (i ≫ p) :=
  hasPreservedColimit_iff_nativeRestriction p i U
    (qCatEquivalenceOfIso (asIso (sliceUnderRestrict p i))).isQCatEquivalence
    (qCatEquivalenceOfIso (asIso (sliceUnderRestrict (p ≫ U) i))).isQCatEquivalence

/-- 一点の元の恒等余錐は任意の関手で余極限に写る。 -/
lemma hasPreservedColimit_pointDiagram {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y) (p : (Δ[0] : SSet.{u}) ⟶ X) :
    HasPreservedColimit U p := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  refine ⟨cosliceIdentityCone x, cosliceIdentityCone_isColimit x, ?_⟩
  apply isColimitCone_of_point_constant _ (U.app (Opposite.op ⦋0⦌) x)
  exact SSet.const_comp x U

/-- 終頂点を持つ形状の余極限は任意の元の関手で保存される。 -/
lemma hasPreservedColimit_of_terminalShapeVertex {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (p : K ⟶ X) (t : K _⦋0⦌) (ht : IsTerminalVertex t) : HasPreservedColimit U p := by
  have := cofinalPointInclusion_mono t
  have := sliceUnderRestrict_trivialKanFibration p (SSet.yonedaEquiv.symm t)
    (F1B.terminalPoint_rightAnodyne ht)
  have := sliceUnderRestrict_trivialKanFibration (p ≫ U) (SSet.yonedaEquiv.symm t)
    (F1B.terminalPoint_rightAnodyne ht)
  apply (hasPreservedColimit_iff_nativeRestriction p (SSet.yonedaEquiv.symm t) U
    (qCatEquivalenceOfTrivialKanFibration
      (sliceUnderRestrict p (SSet.yonedaEquiv.symm t))).isQCatEquivalence
    (qCatEquivalenceOfTrivialKanFibration
      (sliceUnderRestrict (p ≫ U) (SSet.yonedaEquiv.symm t))).isQCatEquivalence).mpr
  exact hasPreservedColimit_pointDiagram U _

end SerrePositivity.InfinityCategories.F2.Ind
