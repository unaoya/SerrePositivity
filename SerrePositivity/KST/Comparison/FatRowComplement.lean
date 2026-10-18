module

public import SerrePositivity.KST.Comparison.FatBoundaryCriterion
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# fat realization の新しい行の境界外の一意性

概要：境界の外の行の元は標準形そのものであり、各行の包含はそこで単射である。
方針：全射の標準形の復元と、標準形の構造体の一意性を使う。
規約：Segal 1974 Proposition 1.6 の骨格の付着の型の pushout の判定。
使われ方：新しい行が境界の外で余計な同一視を持たないこと。
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
概要：指定した次元の標準形は、その次元の行からの包含で表せる。
方針：終域の単体の長さの等式を対象の等式へ移し、全射を標準単体の元と読む。
規約：逆像の標準単体は全射を表す。
使われ方：次の骨格を旧骨格と新しい行で覆うこと。
-/
theorem fatNormalFormRealize_eq_row (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) (n : ℕ) (h : p.degree.len = n) :
    ∃ (x : (F.obj (op ⦋n⦌)).obj d) (t : Δ[n].obj d),
      (fatRealizationInclusion F n).app d (x, t) = fatNormalFormRealize F d p := by
  rcases p with ⟨k, e, he, x⟩
  have hk : k = ⦋n⦌ := SimplexCategory.ext h
  subst k
  exact ⟨x, SSet.stdSimplex.objEquiv.symm e, rfl⟩

/--
概要：境界に入らない二つの行の元は、fat realization の像が同じなら同じである。
方針：両方の単体写像を全射とし、正規化の同値から添字と行の元を復元する。
規約：二つの元は同じ行と内側次数に属する。
使われ方：付着の pushout 判定の境界外の単射性。
-/
theorem fatRealizationInclusion_injective_off_boundary
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (x y : (F.obj (op ⦋n⦌)).obj d) (t u : Δ[n].obj d)
    (ht : t ∉ (SSet.boundary n).obj d) (hu : u ∉ (SSet.boundary n).obj d)
    (h : (fatRealizationInclusion F n).app d (x, t) =
      (fatRealizationInclusion F n).app d (y, u)) : (x, t) = (y, u) := by
  have ht' : Function.Surjective (SSet.stdSimplex.objEquiv t).toOrderHom := by
    by_contra hn
    exact ht hn
  have hu' : Function.Surjective (SSet.stdSimplex.objEquiv u).toOrderHom := by
    by_contra hn
    exact hu hn
  let : Epi (SSet.stdSimplex.objEquiv t) := SimplexCategory.epi_iff_surjective.mpr ht'
  let : Epi (SSet.stdSimplex.objEquiv u) := SimplexCategory.epi_iff_surjective.mpr hu'
  have hn := congrArg (fun z => fatDegreeNormalize F d z) h
  rw [fatDegreeNormalize_inclusion, fatDegreeNormalize_inclusion] at hn
  rw [show fatNormalize F d x (SSet.stdSimplex.objEquiv t) =
      (⟨⦋n⦌, SSet.stdSimplex.objEquiv t, inferInstance, x⟩ : FatNormalForm F d) from
        fatNormalize_of_normalForm F d ⟨⦋n⦌, SSet.stdSimplex.objEquiv t, inferInstance, x⟩,
    show fatNormalize F d y (SSet.stdSimplex.objEquiv u) =
      (⟨⦋n⦌, SSet.stdSimplex.objEquiv u, inferInstance, y⟩ : FatNormalForm F d) from
        fatNormalize_of_normalForm F d ⟨⦋n⦌, SSet.stdSimplex.objEquiv u, inferInstance, y⟩] at hn
  have hp : SSet.stdSimplex.objEquiv t = SSet.stdSimplex.objEquiv u ∧ x = y := by
    simpa only [FatNormalForm.mk.injEq, heq_eq_eq, true_and] using hn
  exact Prod.ext hp.2 (SSet.stdSimplex.objEquiv.injective hp.1)

/--
概要：行の包含は境界の包含の像の補集合で単射である。
方針：境界に属する標準単体は境界の積の射の像に入ることを使う。
規約：型の圏の pushout 判定が要求する像の補集合の形。
使われ方：有限骨格の付着の普遍性。
-/
theorem fatRealizationInclusion_injective_off_boundary_range
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (p q : (F.obj (op ⦋n⦌) ⊗ Δ[n]).obj d)
    (hp : p ∉ Set.range ((F.obj (op ⦋n⦌) ◁ (SSet.boundary n).ι).app d))
    (hq : q ∉ Set.range ((F.obj (op ⦋n⦌) ◁ (SSet.boundary n).ι).app d))
    (h : (fatRealizationInclusion F n).app d p =
      (fatRealizationInclusion F n).app d q) : p = q := by
  apply fatRealizationInclusion_injective_off_boundary F n d p.1 q.1 p.2 q.2
  · intro ht
    exact hp ⟨(p.1, ⟨p.2, ht⟩), rfl⟩
  · intro ht
    exact hq ⟨(q.1, ⟨q.2, ht⟩), rfl⟩
  · exact h

end SerrePositivity.KST.Comparison
