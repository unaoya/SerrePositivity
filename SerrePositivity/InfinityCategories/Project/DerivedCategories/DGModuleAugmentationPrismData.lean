module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationHomotopyComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionProjections
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
/-!
概要：実 augmentation prism の全次数の候補係数を、同じ比較 cochain の切断和で構成する。
方針：混合相には元の augmentation と、相一で切る次数 −1 の比較補正を置く。
規約：現段階は SimplexData。全 HA 方程式と単体作用は別途検証する。
使われ方：実分解 dg 圏上の augmentation の全単体自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 半自由出力射影を全加群の実 dg 圏へ含める。 -/
def dgModuleAugmentationSource :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (RightModule R E) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F).comp
    (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))
/-- 実入力射影の、元の dg 加群値関手による像。 -/
def dgModuleAugmentationTarget :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) (RightModule R E) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).comp F
/-- 同じ実 augmentation の閉次数零の成分。 -/
def dgModuleAugmentationComponent (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val (F.obj X.source)) :=
  _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) X.augmentation)
variable {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 内部切断 j における、実比較 cochain と実左射影の合成補正。 -/
def dgModuleAugmentationPrismCut
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) k := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  let fl := s.hom (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl
  let fr := s.hom (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl
  exact ((I.filter (j < ·)).card : ℤ).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
    (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
    (z := F.obj (s.obj b).source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) _ fr)
    (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _ fl)
    (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega)
/-- 相零から相一へまたぐ全係数。相一で切る同じ実補正を有限和する。 -/
def dgModuleAugmentationPrismMixedHom (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) k :=
  _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
    (z := F.obj (s.obj b).source) (dgModuleAugmentationComponent R C E F (s.obj b)).val
    (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
      (s.hom I a b k hI ha hb hk)) (add_zero k) +
    ∑ j : I, if h : a < j.val ∧ j.val < b ∧ β j.val = 1 then
      dgModuleAugmentationPrismCut R C E F s I a b k hI ha hb hk j.val j.property h.1 h.2.1
      else 0
/-- 二つの相を明示した、同じ実 prism の斉次係数。 -/
def dgModuleAugmentationPrismPhaseHom (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (p q : Fin 2) (hpq : p ≤ q) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (dgModuleAugmentationSource R C E F)
        (dgModuleAugmentationTarget R C E F) p (s.obj a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (dgModuleAugmentationSource R C E F)
        (dgModuleAugmentationTarget R C E F) q (s.obj b)) k := by
  rcases p with ⟨p, hpb⟩
  rcases q with ⟨q, hqb⟩
  cases p with
  | zero =>
    cases q with
    | zero =>
      exact ((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)
    | succ q =>
      have hq0 : q = 0 := by omega
      subst q
      exact dgModuleAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk
  | succ p =>
    have hp0 : p = 0 := by omega
    subst p
    cases q with
    | zero =>
      change (1 : ℕ) ≤ 0 at hpq
      exact False.elim (by omega)
    | succ q =>
      have hq0 : q = 0 := by omega
      subst q
      exact ((dgModuleAugmentationTarget R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)
/-- 全実 prism の対象と斉次係数。全方程式を課す前の実データ。 -/
def dgModuleAugmentationPrismData (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R E) n where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (dgModuleAugmentationSource R C E F)
    (dgModuleAugmentationTarget R C E F) (β i) (s.obj i)
  hom I a b k hI ha hb hk :=
    dgModuleAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk (β a) (β b)
      (β.monotone (show a ≤ b from by
        rw [ha, hb]; exact (I.isLeast_min' _).2 (I.max'_mem _)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
