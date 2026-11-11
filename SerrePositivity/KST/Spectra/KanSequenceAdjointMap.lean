module

public import SerrePositivity.KST.Spectra.KanSequenceCategory

/-!
概要：随伴構造射と可換な各段の射から Kan 列の厳密な射を作る。
方針：suspension と loop の随伴の単射性で構造可換式を戻す。
規約：Kan 条件以外の Ω 条件や単射条件は不要。
使われ方：BF 1978 §2。end の随伴構造の比較を列の射へ束ねる。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section

/-- 随伴構造と可換な段の射は実際の Kan 列の射を与える。 -/
def Hom.ofAdjoint {X Y : KanSequence.{u}}
    (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
    (h : ∀ n, f n ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space
      (Y.sigma n) = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space
        (X.sigma n) ≫ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f (n + 1))) :
    Hom X Y where
  app := f
  comm n := by
    apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (Y.level (n + 1)).space).injective
    change curry (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n) =
      curry (X.sigma n ≫ f (n + 1))
    rw [curry_natural_left, curry_natural_right]
    exact h n

end
end SerrePositivity.KST.Spectra.KanSequence
