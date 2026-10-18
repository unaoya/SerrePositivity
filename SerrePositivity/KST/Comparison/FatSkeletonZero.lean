module

public import SerrePositivity.KST.Comparison.FatSkeletonRowRelations
public import SerrePositivity.KST.Comparison.FatRowComplement

/-!
# fat realization の零骨格

概要：零骨格が第零行と標準零単体の積であることを証明する。
方針：標準形による全射性と、空の境界の外での単射性を使う。
規約：Segal 1974 Proposition 1.6 の骨格帰納の初期段階。
使われ方：零骨格での行の四角形の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：第零行から零骨格への射は同型である。
方針：各次数で境界の外の単射性と、零次元の標準形による全射性を示す。
規約：標準零単体との積を残した表示。
使われ方：有限骨格の比較の帰納の初期段階。
-/
instance fatSkeletonRow_zero_isIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsIso (fatSkeletonRow F 0) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro d
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro p q h
    apply fatRealizationInclusion_injective_off_boundary F 0 d p.1 q.1 p.2 q.2
    · simp [SSet.boundary_zero]
    · simp [SSet.boundary_zero]
    · exact congrArg Subtype.val h
  · intro y
    have heq : (fatDegreeNormalize F d y.1).degree.len = 0 := Nat.eq_zero_of_le_zero y.2
    obtain ⟨x, t, ht⟩ := fatNormalFormRealize_eq_row F d (fatDegreeNormalize F d y.1) 0 heq
    refine ⟨(x, t), ?_⟩
    apply Subtype.ext
    exact ht.trans (fatNormalFormRealize_degreeNormalize F d y.1)

end SerrePositivity.KST.Comparison
