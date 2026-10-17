module
public import SerrePositivity.DifferentialGraded.Perfect.PerfectCompact
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # compact ⇒ Perf に向けた可算 telescope の有限段階因子分解

ここでは任意の列に対する三角圏内の telescope を扱う。
semifree filtration の余極限との比較、有限 cell への因子分解は別の課題である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_hom_ext_zero {J : Type u} {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (F : J → DerivedModuleCategory A D)
    (f : X ⟶ ∐ F) (hf : ∀ n, f ≫ moduleDerivedCoproductProjection A D F n = 0) :
    f = 0 := by
  classical
  obtain ⟨t, g, hg⟩ := hX J F f
  have hgi (i : J) (hi : i ∈ t) : g i = 0 := by
    have h := congrArg (fun k => k ≫ moduleDerivedCoproductProjection A D F i) hg
    rw [sum_comp, hf] at h
    rw [Finset.sum_eq_single i] at h
    · simpa only [Category.assoc, moduleDerivedCoproductProjection_self,
        Category.comp_id] using h
    · intro j _ hji
      rw [Category.assoc, moduleDerivedCoproductProjection_ne A D F j i hji, comp_zero]
    · exact fun h => (h hi).elim
  rw [← hg]
  exact Finset.sum_eq_zero (fun i hi => by rw [hgi i hi, zero_comp])

variable (F : ℕ → DerivedModuleCategory A D) (d : ∀ n, F n ⟶ F (n + 1))

/-- 可算添字を u に持ち上げ、既存の compact API と同じ余積を使う。 -/
abbrev moduleTelescopeFamily (n : ULift.{u} ℕ) := F n.down

def moduleTelescopeShift : (∐ moduleTelescopeFamily A D F) ⟶ ∐ moduleTelescopeFamily A D F :=
  Sigma.desc (fun n => d n.down ≫ Sigma.ι (moduleTelescopeFamily A D F) ⟨n.down + 1⟩)

def moduleTelescopeMap : (∐ moduleTelescopeFamily A D F) ⟶ ∐ moduleTelescopeFamily A D F :=
  𝟙 _ - moduleTelescopeShift A D F d

lemma moduleTelescopeShift_projection_zero :
    moduleTelescopeShift A D F d ≫
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨0⟩ = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [moduleTelescopeShift, Category.assoc, moduleDerivedCoproductProjection]

lemma moduleTelescopeShift_projection_succ (n : ℕ) :
    moduleTelescopeShift A D F d ≫
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n + 1⟩ =
      moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n⟩ ≫ d n := by
  apply Sigma.hom_ext
  intro ⟨i⟩
  by_cases h : i = n
  · subst i
    simp only [moduleTelescopeShift, Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [moduleDerivedCoproductProjection_self, Category.comp_id, ← Category.assoc,
      moduleDerivedCoproductProjection_self, Category.id_comp]
  · simp only [moduleTelescopeShift, Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [moduleDerivedCoproductProjection_ne A D (moduleTelescopeFamily A D F)
      ⟨i + 1⟩ ⟨n + 1⟩ (by simp; omega), comp_zero, ← Category.assoc,
      moduleDerivedCoproductProjection_ne A D (moduleTelescopeFamily A D F) ⟨i⟩ ⟨n⟩
        (by simpa using h), zero_comp]

/-- compact な始域の Hom 上では 1-shift は単射。 -/
lemma moduleCompact_telescopeMap_zero {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (f : X ⟶ ∐ moduleTelescopeFamily A D F)
    (hf : f ≫ moduleTelescopeMap A D F d = 0) : f = 0 := by
  have he : f = f ≫ moduleTelescopeShift A D F d := by
    simpa only [moduleTelescopeMap, comp_sub, Category.comp_id, sub_eq_zero] using hf
  apply moduleCompact_hom_ext_zero A D hX (moduleTelescopeFamily A D F) f
  intro ⟨n⟩
  induction n with
  | zero => rw [he, Category.assoc, moduleTelescopeShift_projection_zero, comp_zero]
  | succ n ih =>
    calc
      _ = f ≫ moduleTelescopeShift A D F d ≫
          moduleDerivedCoproductProjection A D (moduleTelescopeFamily A D F) ⟨n + 1⟩ := by
            rw [← Category.assoc, ← he]
      _ = 0 := by rw [moduleTelescopeShift_projection_succ, ← Category.assoc, ih, zero_comp]

lemma moduleCompact_shiftedTelescopeMap_zero {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X)
    (f : X ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hf : f ≫ (moduleTelescopeMap A D F d)⟦(1 : ℤ)⟧' = 0) : f = 0 := by
  let E := shiftEquiv' (DerivedModuleCategory A D) (-1 : ℤ) 1 (by omega)
  have : E.functor.Additive :=
    inferInstanceAs (shiftFunctor (DerivedModuleCategory A D) (-1 : ℤ)).Additive
  let e := E.toAdjunction.homAddEquiv X (∐ moduleTelescopeFamily A D F)
  let a := e.symm f
  have ha : a ≫ moduleTelescopeMap A D F d = 0 := by
    apply e.injective
    rw [map_zero]
    change E.toAdjunction.homEquiv _ _ (a ≫ _) = 0
    rw [E.toAdjunction.homEquiv_naturality_right]
    change e a ≫ _ = 0
    rw [show e a = f from e.apply_symm_apply f]
    exact hf
  have ha0 := moduleCompact_telescopeMap_zero A D F d (moduleCompact_shift A D hX (-1)) a ha
  calc
    f = e a := (e.apply_symm_apply f).symm
    _ = 0 := by rw [ha0, map_zero]

/-- 任意の telescope 三角形への射は、余積の有限個の成分を経由する。 -/
lemma moduleCompact_telescope_finite_lift {X Y : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) (f : X ⟶ Y) :
    ∃ (t : Finset (ULift.{u} ℕ)) (g : ∀ n, X ⟶ F n.down),
      f = ∑ n ∈ t, g n ≫ Sigma.ι (moduleTelescopeFamily A D F) n ≫ c := by
  have hz : b ≫ (moduleTelescopeMap A D F d)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  have hfb : f ≫ b = 0 := moduleCompact_shiftedTelescopeMap_zero A D F d hX (f ≫ b)
    (by rw [Category.assoc, hz, comp_zero])
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f hfb
  change f = g ≫ c at hg
  obtain ⟨t, a, ha⟩ := hX (ULift.{u} ℕ) (moduleTelescopeFamily A D F) g
  refine ⟨t, a, ?_⟩
  rw [hg, ← ha, sum_comp]
  simp only [Category.assoc]

/-- compact な対象から telescope への射は一つの有限段階を経由する。 -/
lemma moduleCompact_telescope_factor {X Y : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ Y)
    (b : Y ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) (f : X ⟶ Y) :
    ∃ (n : ℕ) (g : X ⟶ F n),
      f = g ≫ Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c := by
  classical
  let j (n : ℕ) := Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c
  have hj (n : ℕ) : d n ≫ j (n + 1) = j n := by
    have h := congrArg (fun k => Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ k)
      (comp_distTriang_mor_zero₁₂ _ hT)
    change _ ≫ (moduleTelescopeMap A D F d ≫ c) = _ at h
    have he : j n = d n ≫ j (n + 1) := by
      simpa only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, sub_comp,
        Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
        comp_zero, sub_eq_zero, j] using h
    exact he.symm
  let α : Functor.ofSequence d ⟶ (Functor.const ℕ).obj Y :=
    NatTrans.ofSequence j (by intro n; simpa using hj n)
  obtain ⟨t, a, ha⟩ := moduleCompact_telescope_finite_lift A D F d hX c b hT f
  let N := t.sup (fun n => n.down)
  refine ⟨N, ∑ n ∈ t, (if hn : n.down ≤ N then
    a n ≫ (Functor.ofSequence d).map (homOfLE hn) else 0), ?_⟩
  rw [sum_comp, ha]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n.down ≤ N := Finset.le_sup (f := fun n => n.down) hn
  rw [dite_eq_left hnN, Category.assoc]
  have h := α.naturality (homOfLE hnN)
  change (Functor.ofSequence d).map _ ≫ j N = j n.down ≫ 𝟙 Y at h
  rw [Category.comp_id] at h
  exact (congrArg (fun k => a n ≫ k) h).symm

/-- compact な telescope 対象は、有限高さの一段階の retract である。 -/
lemma moduleCompact_telescope_retract {X : DerivedModuleCategory A D}
    (hX : moduleCompact A D X) (c : (∐ moduleTelescopeFamily A D F) ⟶ X)
    (b : X ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) :
    ∃ n : ℕ, Nonempty (Retract X (F n)) := by
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D F d hX c b hT (𝟙 X)
  exact ⟨n, ⟨{
    i := g
    r := Sigma.ι (moduleTelescopeFamily A D F) ⟨n⟩ ≫ c
    retract := hg.symm }⟩⟩

end SerrePositivity.DifferentialGraded
