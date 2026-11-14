module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Tactic.Order

/-! # Coproduct closure from cobase change and transfinite composition

The summands are replaced one at a time. The stage diagram is a coproduct of
step diagrams, each of which is eventually constant below any limit stage.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.MorphismClosure

variable {C : Type u} [Category.{v} C]

section Step
variable {J : Type w} [LinearOrder J] {A B : C} (f : A ⟶ B) (i : J)

abbrev stepObj (_f : A ⟶ B) (i j : J) : C := if i < j then B else A

def stepMap {j k : J} (h : j ≤ k) : stepObj f i j ⟶ stepObj f i k :=
  if hj : i < j then
    eqToHom (show stepObj f i j = B by simp [stepObj, hj]) ≫
      eqToHom (show B = stepObj f i k by simp [stepObj, lt_of_lt_of_le hj h])
  else if hk : i < k then
    eqToHom (show stepObj f i j = A by simp [stepObj, hj]) ≫ f ≫
      eqToHom (show B = stepObj f i k by simp [stepObj, hk])
  else eqToHom (by simp [stepObj, hj, hk])

abbrev step : J ⥤ C where
  obj := stepObj f i
  map φ := stepMap f i (leOfHom φ)
  map_id j := by
    classical
    by_cases hj : i < j <;> simp [stepMap, hj]
  map_comp {j k l} φ ψ := by
    classical
    have hjk := leOfHom φ
    have hkl := leOfHom ψ
    by_cases hj : i < j <;> by_cases hk : i < k <;> by_cases hl : i < l
    all_goals first | (exfalso; order) | simp [stepMap, hj, hk, hl, stepObj]

lemma stepMap_isIso {j k : J} (h : j ≤ k) (heq : (i < j) ↔ (i < k)) :
    IsIso (stepMap f i h) := by
  classical
  by_cases hj : i < j
  · have hk := heq.mp hj
    simp only [stepMap, dite_eq_left hj]
    infer_instance
  · have hk : ¬ i < k := fun hk ↦ hj (heq.mpr hk)
    simp only [stepMap, dite_eq_right hj, dite_eq_right hk]
    infer_instance

variable [OrderBot J] [SuccOrder J]

instance step_isWellOrderContinuous : (step f i).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    classical
    let F := (Set.principalSegIio m).monotone.functor ⋙ step f i
    obtain ⟨j, hj, heq⟩ : ∃ j : J, j < m ∧ ((i < j) ↔ (i < m)) := by
      by_cases h : i < m
      · exact ⟨Order.succ i, hm.succ_lt h, iff_of_true
          (Order.lt_succ_of_not_isMax (not_isMax_of_lt h)) h⟩
      · exact ⟨⊥, hm.bot_lt, iff_of_false (not_lt_of_ge bot_le) h⟩
    let j₀ : Set.Iio m := ⟨j, hj⟩
    have : Nonempty (Set.Iio m) := ⟨j₀⟩
    have hF : F.IsEventuallyConstantFrom j₀ := by
      intro k φ
      change IsIso (stepMap f i (leOfHom φ : j ≤ k.val))
      apply stepMap_isIso f i (leOfHom φ : j ≤ k.val)
      exact ⟨fun h ↦ lt_of_lt_of_le h (leOfHom φ),
        fun h ↦ heq.mpr (lt_trans h k.property)⟩
    have : IsIso (((Set.principalSegIio m).cocone (step f i)).ι.app j₀) :=
      stepMap_isIso f i hj.le heq
    exact ⟨hF.isColimitOfIsIso _⟩

end Step

lemma sigma_isoColimit_naturality {ι : Type w} [HasCoproducts.{w} C]
    {F G : Discrete ι ⥤ C} (φ : F ⟶ G) :
    (Sigma.isoColimit F).hom ≫ colimMap φ =
      Limits.Sigma.map (fun i ↦ φ.app ⟨i⟩) ≫ (Sigma.isoColimit G).hom := by
  apply Sigma.hom_ext
  intro i
  simp

section Stages
variable {J ι : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) (a : ι → J)

abbrev mixedFamily : J ⥤ Discrete ι ⥤ C :=
  (Discrete.functor (fun i ↦ step (f i) (a i))).flip

instance mixedFamily_isWellOrderContinuous : (mixedFamily f a).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨evaluationJointlyReflectsColimits _ (fun ⟨i⟩ ↦ by
    change IsColimit ((Set.principalSegIio m).cocone (step (f i) (a i)))
    exact (step (f i) (a i)).isColimitOfIsWellOrderContinuous m hm)⟩

variable [HasCoproducts.{w} C]

abbrev stages : J ⥤ C := mixedFamily f a ⋙ colim

instance stages_isWellOrderContinuous : (stages f a).IsWellOrderContinuous := by
  have : PreservesWellOrderContinuousOfShape J (colim : (Discrete ι ⥤ C) ⥤ C) :=
    ⟨fun _ _ ↦ inferInstance⟩
  exact inferInstanceAs (mixedFamily f a ⋙ colim).IsWellOrderContinuous

end Stages

/-- A coproduct map with just one noninvertible component is a cobase change
of that component. -/
lemma isPushout_sigma_single {ι : Type w} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) [HasCoproduct A] [HasCoproduct B]
    (j : ι) (h : ∀ i, i ≠ j → IsIso (f i)) :
    IsPushout (Sigma.ι A j) (f j) (Limits.Sigma.map f) (Sigma.ι B j) := by
  classical
  let sq : CommSq (Sigma.ι A j) (f j) (Limits.Sigma.map f) (Sigma.ι B j) := ⟨by simp⟩
  apply IsPushout.of_isColimit' sq
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ Sigma.desc (fun i ↦ if hi : i = j then
      eqToHom (congrArg B hi) ≫ s.inr else
      have := h i hi
      inv (f i) ≫ Sigma.ι A i ≫ s.inl)) ?_ ?_ ?_
  · intro s
    apply Sigma.hom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simpa using s.condition.symm
    · have := h i hi
      simp [hi]
  · intro s
    simp
  · intro s m hl hr
    apply Sigma.hom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simpa using hr
    · have := h i hi
      simp only [Sigma.ι_comp_desc, dite_eq_right hi]
      rw [← cancel_epi (f i)]
      simpa using (Sigma.ι A i) ≫= hl

section OrderedFamily
variable {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    [OrderBot (WithTop ι)] [SuccOrder (WithTop ι)]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) [HasCoproducts.{w} C]

abbrev orderedStages : WithTop ι ⥤ C := stages f (fun i ↦ (i : WithTop ι))

def orderedStages_arrowIso :
    Arrow.mk ((orderedStages f).map (homOfLE bot_le : (⊥ : WithTop ι) ⟶ ⊤)) ≅
      Arrow.mk (Limits.Sigma.map f) := by
  classical
  let e₀ : (mixedFamily f (fun i ↦ (i : WithTop ι))).obj ⊥ ≅ Discrete.functor A :=
    Discrete.natIso (fun ⟨i⟩ ↦ eqToIso (by simp [mixedFamily, step, stepObj]))
  let e₁ : (mixedFamily f (fun i ↦ (i : WithTop ι))).obj ⊤ ≅ Discrete.functor B :=
    Discrete.natIso (fun ⟨i⟩ ↦ eqToIso (by simp [mixedFamily, step, stepObj]))
  exact (Functor.mapArrow colim).mapIso (Arrow.isoMk
    (f := Arrow.mk ((mixedFamily f (fun i ↦ (i : WithTop ι))).map
      (homOfLE bot_le : (⊥ : WithTop ι) ⟶ ⊤)))
    (g := Arrow.mk (Discrete.natTrans (fun ⟨i⟩ ↦ f i))) e₀ e₁ (by
    ext ⟨i⟩
    simp [e₀, e₁, mixedFamily, step, stepMap, stepObj, eqToIso]))

set_option backward.isDefEq.respectTransparency false in
omit [WellFoundedLT ι] [OrderBot (WithTop ι)] in
lemma orderedStages_succ_mem (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (hf : ∀ i, P (f i)) (j : WithTop ι) (hj : ¬IsMax j) :
    P ((orderedStages f).map (homOfLE (Order.le_succ j))) := by
  classical
  have htop : j ≠ ⊤ := by simpa only [isMax_iff_eq_top] using hj
  obtain ⟨j, rfl⟩ := WithTop.ne_top_iff_exists.mp htop
  let g (i : ι) := (step (f i) (i : WithTop ι)).map
    (homOfLE (Order.le_succ (j : WithTop ι)))
  have hg : P (g j) := by
    simpa [g, step, stepMap, stepObj,
      Order.lt_succ_of_not_isMax hj, P.cancel_left_of_respectsIso,
      P.cancel_right_of_respectsIso] using hf j
  have hother : ∀ i, i ≠ j → IsIso (g i) := by
    intro i hij
    apply stepMap_isIso (f i) (i : WithTop ι) (Order.le_succ _)
    rw [Order.lt_succ_iff_of_not_isMax hj]
    constructor
    · exact le_of_lt
    · intro h
      exact lt_of_le_of_ne h (by simpa using hij)
  have hp := P.of_isPushout (isPushout_sigma_single g j hother) hg
  let G := mixedFamily f (fun i ↦ (i : WithTop ι))
  let e : Arrow.mk (Limits.Sigma.map g) ≅
      Arrow.mk ((orderedStages f).map (homOfLE (Order.le_succ (j : WithTop ι)))) :=
    Arrow.isoMk (Sigma.isoColimit (G.obj (j : WithTop ι)))
      (Sigma.isoColimit (G.obj (Order.succ (j : WithTop ι)))) (by
        exact sigma_isoColimit_naturality
          (G.map (homOfLE (Order.le_succ (j : WithTop ι)))))
  exact (P.arrow_mk_iso_iff e).mp hp

lemma sigma_mem_of_ordered (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}] (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  let F := orderedStages f
  let d : P.TransfiniteCompositionOfShape (WithTop ι)
      (F.map (homOfLE bot_le : (⊥ : WithTop ι) ⟶ ⊤)) :=
    { F := F
      isoBot := Iso.refl _
      incl := { app j := F.map (homOfLE le_top)
                naturality j k φ := by
                  dsimp
                  rw [Category.comp_id, ← F.map_comp]
                  rfl }
      isColimit := colimitOfDiagramTerminal isTerminalTop F
      map_mem := orderedStages_succ_mem f P hf }
  exact (P.arrow_mk_iso_iff (orderedStages_arrowIso f)).mp
    (P.transfiniteCompositionsOfShape_le (WithTop ι) _ ⟨d⟩)

end OrderedFamily

/-- Well-ordering the index costs no extra closure hypothesis, and includes the
empty family via the one-object ordered stage category. -/
lemma sigma_mem (P : MorphismProperty C) [HasCoproducts.{w} C]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}]
    {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have : WellFoundedLT ι := WellOrderingRel.isWellOrder.wf
  let : OrderBot (WithTop ι) := WellFoundedLT.toOrderBot _
  let : SuccOrder (WithTop ι) := SuccOrder.ofLinearWellFoundedLT _
  exact sigma_mem_of_ordered f P hf

/-- The coproduct closure needed by Smith's theorem is a consequence of its
pushout and transfinite-composition assumptions. -/
lemma stableUnderCoproducts (P : MorphismProperty C) [HasCoproducts.{w} C]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}] :
    P.IsStableUnderCoproducts.{w} where
  isStableUnderCoproductsOfShape _ι :=
    MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
      (fun _ _ _ _ f hf ↦ sigma_mem P f hf)

end SerrePositivity.MorphismClosure

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.1.2.5" (partial := stronger-hyp) "仮定：原典の C に加え Mathlib IsLocallyPresentable C、局所小性と一つの colimit universe を明示し、生成射の類は小さい（Lean の形式的仮定が強い）。結論：I.rlp.llp と I.rlp の同じ functorial factorization があり、生成射の両端が κ-presentable なら指定分解の全 arrow factors が κ-filtered colimits を保つ。generatedLeft_le_of_closed と coproduct closure により左類は最小の弱飽和類に入り、原典の二結論に一致。この Mathlib presentability と原典の poset 型定義の完全な比較は含まない。"] _root_.SerrePositivity.MorphismClosure.stableUnderCoproducts
attribute [cite HTT "A.1.2.7" (partial := stronger-hyp) "仮定：小さい生成射の類 I、C は Mathlib IsLocallyPresentable（Lean の形式的仮定が強い）。結論：I⊆I.rlp.llp、任意の weakly saturated P⊇I に I.rlp.llp⊆P となり、原典の最小性に一致。I.rlp.llp の三閉性は ordinary lifting-class の既存 instances で与えられる。HTT の presentable の四条件からの比較は別途必要。"] _root_.SerrePositivity.MorphismClosure.stableUnderCoproducts
