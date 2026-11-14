module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugInjectiveReindex
/-!
概要：非単射な引き戻し係数への同じ実比較 cochain の作用が零になることを証明する。
方針：高次係数の零と、潰れた二点係数の単位を同じ全次数の単位零式へ移す。
規約：退化係数を選び直さない。使われ方：実混合候補の非単射引き戻し。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
/-- 全整数次数で、同じ実比較成分は零を零へ送る。 -/
lemma dgCommaAugmentationHomotopyComponent_zero
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (k : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y k 0 = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent, map_zero]
/-- 同じ実比較成分は、次数零の実単位に対して零。 -/
lemma dgCommaAugmentationHomotopyComponent_unitElement
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X X 0 (unitElement R X).val = 0 := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X X 0
    ((eId (_root_.SerrePositivity.DifferentialGraded.Complex R) X).f 0 (1 : R)) = 0
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent_unit R C E F X 0 (1 : R)
/-- 端点・次数の等式と同じ実単位との異種等号は、比較成分の零を与える。 -/
lemma dgCommaAugmentationHomotopyComponent_zero_of_heq_unit
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (k : ℤ) (z : GradedHom R X Y k)
    (hXY : X = Y) (hk : k = 0) (hz : HEq z (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F X Y k z = 0 := by
  cases hXY
  subst k
  rw [eq_of_heq hz]
  exact dgCommaAugmentationHomotopyComponent_unitElement R C E F X
/-- 非単射な実引き戻し係数への比較成分は、潰れた辺も含めて全次数で零。 -/
lemma dgCommaAugmentationHomotopyComponent_pullback_zero_of_not_inj
    {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F ((s.pullback α).obj a)
      ((s.pullback α).obj b) k ((s.pullback α).hom I a b k hI ha hb hk) = 0 := by
  by_cases hc : I.card = 2
  · have hXY : (s.pullback α).obj a = (s.pullback α).obj b :=
      congrArg s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
        (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _))
    have hk0 : k = 0 := by omega
    exact dgCommaAugmentationHomotopyComponent_zero_of_heq_unit R C E F
      ((s.pullback α).obj a) ((s.pullback α).obj b) k _ hXY hk0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α I a b k hI ha hb hk hi hc)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α I a b k hI ha hb hk hi hc,
      dgCommaAugmentationHomotopyComponent_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
