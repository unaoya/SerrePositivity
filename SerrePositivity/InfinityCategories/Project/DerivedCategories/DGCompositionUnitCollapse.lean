module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionNaturality
/-!
概要：dg 合成の右単位退化に使う切替後の頂点の終点への縮約を定める。
方針：切替前を保ち、切替後を最後の頂点へ写す単調写像の path 座標を計算する。
規約：全次数と全二値ラベルを保持する。
使われ方：coherent dg 合成 prism の第二入力が恒等射の場合の退化表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SimplicialThickening SSet
open scoped _root_.Simplicial

def dgCompositionUnitCollapse {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    Fin (n + 2) →o Fin (n + 2) where
  toFun := Fin.lastCases (Fin.last (n + 1))
    (fun i => if t i = 0 then i.castSucc else Fin.last (n + 1))
  monotone' := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      have h : j = Fin.last (n + 1) := le_antisymm (Fin.le_last _) hij
      subst j
      exact le_rfl
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        split <;> exact Fin.le_last _
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        by_cases hi : t i = 0 <;> by_cases hj : t j = 0
        · simp only [hi, hj, ite_true]
          exact hij
        · simp only [hi, hj, ite_true, ite_false]
          exact Fin.le_last _
        · have h := t.monotone (Fin.castSucc_le_castSucc_iff.mp hij)
          rw [hj] at h
          exact (hi (le_antisymm h (Fin.zero_le _))).elim
        · simp only [hi, hj, ite_false]
          exact le_rfl

lemma dgCompositionUnitCollapse_last {n : ℕ} (t : Fin (n + 1) →o Fin 2) :
    dgCompositionUnitCollapse t (Fin.last (n + 1)) = Fin.last (n + 1) := by
  simp [dgCompositionUnitCollapse]
lemma dgCompositionUnitCollapse_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 0) :
    dgCompositionUnitCollapse t i.castSucc = i.castSucc := by
  simp [dgCompositionUnitCollapse, hi]
lemma dgCompositionUnitCollapse_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i ≠ 0) :
    dgCompositionUnitCollapse t i.castSucc = Fin.last (n + 1) := by
  simp [dgCompositionUnitCollapse, hi]

def dgCompositionUnitCollapsePath {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (hj : dgCompositionUnitCollapse t j = Fin.last (n + 1))
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := (fun k : ULift.{u} (Fin (n + 2)) =>
    ULift.up (dgCompositionUnitCollapse t k.down)) '' P.I
  left := ⟨ULift.up i.castSucc, P.left,
    ULift.ext (dgCompositionUnitCollapse_zero t i hi)⟩
  right := ⟨ULift.up j, P.right, ULift.ext hj⟩
  left_le k hk := by
    rcases hk with ⟨l, hl, rfl⟩
    have h := (dgCompositionUnitCollapse t).monotone (P.left_le l hl)
    change i.castSucc ≤ dgCompositionUnitCollapse t l.down
    simpa only [dgCompositionUnitCollapse_zero t i hi] using h
  le_right k hk := by
    rcases hk with ⟨l, hl, rfl⟩
    change dgCompositionUnitCollapse t l.down ≤ Fin.last (n + 1)
    exact Fin.le_last _

lemma dgCompositionUnitCollapsePath_maximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (hj : dgCompositionUnitCollapse t j = Fin.last (n + 1))
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (dgCompositionUnitCollapsePath t hi hj P) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P := by
  apply le_antisymm
  · obtain ⟨⟨k⟩, hk, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (dgCompositionUnitCollapsePath t hi hj P)
    have he' := congrArg ULift.down he
    dsimp only at he'
    induction k using Fin.lastCases with
    | last =>
      simp only [dgCompositionUnitCollapse_last] at he'
      exact (Fin.castSucc_ne_last _ he'.symm).elim
    | cast k =>
      by_cases ht : t k = 0
      · rw [dgCompositionUnitCollapse_zero t k ht] at he'
        have he'' := Fin.castSucc_injective _ he'
        rw [← he'']
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.le_pathCutMaximum t hi P k ht hk
      · rw [dgCompositionUnitCollapse_one t k ht] at he'
        exact (Fin.castSucc_ne_last _ he'.symm).elim
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum
    exact ⟨ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum t hi P).castSucc,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi P).2,
      ULift.ext (dgCompositionUnitCollapse_zero t _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum_spec t hi P).1)⟩
def dgCompositionUnitCollapsePathFunctor {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2))
    (hj : dgCompositionUnitCollapse t j = Fin.last (n + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j) ⥤
      Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1))) where
  obj := dgCompositionUnitCollapsePath t hi hj
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

lemma dgCompositionUnitCollapseHom {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2))
    (hj : dgCompositionUnitCollapse t j = Fin.last (n + 1)) :
    (SimplicialThickening.functor (dgCompositionUnitCollapse t).uliftMap).map
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) => SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
          (dgCompositionUnitCollapse_zero t i hi) hj) =
      nerveMap (dgCompositionUnitCollapsePathFunctor t hi j hj) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
        (dgCompositionUnitCollapse_zero t i hi))
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))) hj)
    (((SimplicialThickening.functor (dgCompositionUnitCollapse t).uliftMap).map
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j⟩).app d P) k

lemma dgCompositionUnitCollapseHom_maximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) (j : Fin (n + 2))
    (hj : dgCompositionUnitCollapse t j = Fin.last (n + 1)) :
    nerveMap (dgCompositionUnitCollapsePathFunctor.{u} t hi j hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d
    ((nerveMap (dgCompositionUnitCollapsePathFunctor t hi j hj)).app d P)).down.toOrderHom k = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply]
  exact dgCompositionUnitCollapsePath_maximum t hi hj (P.obj k)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
