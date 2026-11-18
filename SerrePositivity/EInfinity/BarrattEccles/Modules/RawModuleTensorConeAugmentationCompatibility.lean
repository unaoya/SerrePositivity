module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationPositive
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationEdge
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationOrdinary
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の実 cone の全斉次成分は、同じ対象ごとの augmentation と厳密に両立する。
方針：零次は混合・通常辺の合成式、他の次数は正次成分の消滅を使う。
規約：全有限集合・全次数の元の式を保つ。使われ方：終端 X を加えた二重 cone の HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits

open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0) =
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c a)).val := by
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : (0 : Fin (n + 2)) ∈ I := by rw [ha]; exact I.min'_mem _
    exact eq_of_heq
      (strictRawModuleTensorConeAugmentationAt_compose_mixed_pair A X P Q c I 0 b hI ha hb hk rfl h0)
  · exact strictRawModuleTensorConeAugmentationAt_compose_ordinary_pair A X P Q c I a b hI ha hb hk ha0

lemma strictRawModuleTensorConeAugmentationAt_compose {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk) (add_zero k) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c a) k := by
  by_cases hk0 : k = 0
  · subst hk0
    exact (strictRawModuleTensorConeAugmentationAt_compose_pair A X P Q c I a b hI ha hb hk).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero
        (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (strictRawModuleTensorConeAugmentationAt A X P Q c a)).symm
  · exact (strictRawModuleTensorConeAugmentationAt_compose_of_card_ge_three A X P Q c I a b k
      hI ha hb hk (by omega)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne
        (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (strictRawModuleTensorConeAugmentationAt A X P Q c a) k hk0).symm

end SerrePositivity.EInfinity.BarrattEccles
