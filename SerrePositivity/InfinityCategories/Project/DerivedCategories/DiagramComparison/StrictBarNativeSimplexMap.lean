module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeMixedComparison

/-!
概要：元の strict 自然変換から、元の native 余錐の全 HA 単体間の厳密写像を構成する。
方針：旧成分と apex へ届く成分の、証明した二つの可換式を合わせる。
規約：自然性を入力に追加せず、元の余錐の全成分を使う。
使われ方：3b-3 R6、元の指定余錐の全パラメーター族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の native 余錐の全 HA 単体間の、元の同じ閉零成分による厳密写像。 -/
def strictBarNativeSimplexMap {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    StrictSimplexMap A (RightModule A PUnit.{1})
      (strictBarNativeSimplex A J F s).toSimplexData (strictBarNativeSimplex A J G s).toSimplexData where
  app i := strictBarNativeSimplexApp A J η s i
  naturality T a b k hT ha hb hk := by
    by_cases hbl : b = Fin.last (n + 1)
    · subst hbl
      induction a using Fin.lastCases with
      | last =>
        have h := T.min'_lt_max'_of_card (by omega)
        rw [← ha, ← hb] at h
        exact (lt_irrefl _ h).elim
      | cast a => exact strictBarNativeMixed_naturality A J η s T a k hT ha hb hk
    · exact strictBarNativeOld_naturality A J η s T a b k hT ha hb hk hbl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
