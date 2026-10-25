module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplexData
/-!
概要：元の coherent 単体へ正規化実 bar を加えた全 HA 単体を作る。
方針：末端部分集合は twisting 式で、末端を含まない部分集合は元の先頭面から判定する。
規約：全次元・全部分集合の方程式を保つ。自然性と余錐の普遍性は後続で証明する。
使われ方：正規化 native 余錐の単体写像の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNativeSimplexData_old_equation {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hl : Fin.last (n + 1) ∉ J) :
    (dgCoherentBarNativeSimplexData R D F hMC s).Equation J := by
  have h := SimplexData.equation_image_of_pullback
    (dgCoherentBarNativeSimplexData R D F hMC s) Fin.castSuccOrderEmb.toOrderHom
    (coherentDiagramSimplex F s) (dgCoherentBarNativeSimplexData_front R D F hMC s)
    (PinchedHom.withoutLast J) (Fin.castSucc_injective _).injOn
  have he : (PinchedHom.withoutLast J).image Fin.castSuccOrderEmb.toOrderHom = J := by
    change (PinchedHom.withoutLast J).image Fin.castSucc = J
    rw [PinchedHom.image_withoutLast, Finset.erase_eq_of_notMem hl]
  simpa only [he] using h

def dgCoherentBarNativeSimplex {n : ℕ} (s : I _⦋n⦌) :
    DGNerve.Simplex R (RightModule R D) (n + 1) where
  toSimplexData := dgCoherentBarNativeSimplexData R D F hMC s
  equation J a b k hJ ha hb hk := by
    by_cases hbl : b = Fin.last (n + 1)
    · cases hbl
      exact dgCoherentBarNativeSimplexData_last_equation R D F hMC s J a k hJ ha hb hk
    · have hl : Fin.last (n + 1) ∉ J := by
        intro hl
        apply hbl
        apply le_antisymm (Fin.le_last b)
        rw [hb]
        exact (J.isGreatest_max' (Index.nonempty hJ)).2 hl
      exact dgCoherentBarNativeSimplexData_old_equation R D F hMC s J hl a b k hJ ha hb hk

lemma dgCoherentBarNativeSimplex_front {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplex R D F hMC s).pullback Fin.castSuccOrderEmb.toOrderHom =
      coherentDiagramSimplex F s := by
  apply DGNerve.Simplex.ext
  exact dgCoherentBarNativeSimplexData_front R D F hMC s

lemma dgCoherentBarNativeSimplex_last {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)) =
      dgCoherentBarNormalizedModule R D F hMC :=
  SimplexData.lastReplacementObj_last _ _

end SerrePositivity.InfinityCategories
