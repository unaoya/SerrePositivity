module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplexData
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNativeSimplexData_old_equation {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hl : Fin.last (n + 1) ∉ J) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC s).Equation J := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.equation_image_of_pullback
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC s) Fin.castSuccOrderEmb.toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_front R D F hMC s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J) (Fin.castSucc_injective _).injOn
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).image Fin.castSuccOrderEmb.toOrderHom = J := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).image Fin.castSucc = J
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withoutLast, Finset.erase_eq_of_notMem hl]
  simpa only [he] using h

def dgCoherentBarNativeSimplex {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) (n + 1) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData R D F hMC s
  equation J a b k hJ ha hb hk := by
    by_cases hbl : b = Fin.last (n + 1)
    · cases hbl
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_last_equation R D F hMC s J a k hJ ha hb hk
    · have hl : Fin.last (n + 1) ∉ J := by
        intro hl
        apply hbl
        apply le_antisymm (Fin.le_last b)
        rw [hb]
        exact (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)).2 hl
      exact dgCoherentBarNativeSimplexData_old_equation R D F hMC s J hl a b k hJ ha hb hk

lemma dgCoherentBarNativeSimplex_front {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplex R D F hMC s).pullback Fin.castSuccOrderEmb.toOrderHom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_front R D F hMC s

lemma dgCoherentBarNativeSimplex_last {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
