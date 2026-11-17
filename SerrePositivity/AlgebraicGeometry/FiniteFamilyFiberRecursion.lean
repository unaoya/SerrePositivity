module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：混合した有限族のファイバー積を、先頭と末尾の Cartesian square に分ける。
方針：同じ wide pullback の射影と普遍性を使う。
規約：同じ基底と元の全ての対象・射影を保持する。
使われ方：有限余積と元の Čech nerve の比較の帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {S : C}

/-- 同じ一個の族の wide pullback の射影は、その元の対象との同型。 -/
def finiteFamilyFiberZeroIso {X : Fin 1 → C} (f : ∀ j, X j ⟶ S) :
    widePullback S X f ≅ X 0 where
  hom := WidePullback.π f 0
  inv := WidePullback.lift (f 0)
    (fun j ↦ eqToHom (congrArg X (Subsingleton.elim 0 j))) (by
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [Category.assoc, WidePullback.lift_π, eqToHom_refl,
        Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, WidePullback.lift_base,
        WidePullback.π_arrow, Category.id_comp]
  inv_hom_id := by simp only [WidePullback.lift_π, eqToHom_refl]

/-- 同じ混合族のファイバー積は、末尾と先頭の元の基底上の pullback。 -/
theorem isPullback_finiteFamilyFiberSucc (n : ℕ) {X : Fin (n + 2) → C}
    (f : ∀ j, X j ⟶ S) :
    let t := WidePullback.lift (WidePullback.base f)
      (fun i : Fin (n + 1) ↦ WidePullback.π f i.succ)
      (fun i ↦ WidePullback.π_arrow f i.succ)
    IsPullback t (WidePullback.π f 0) (WidePullback.base (fun i : Fin (n + 1) ↦ f i.succ)) (f 0) := by
  dsimp only
  have h : WidePullback.lift (WidePullback.base f)
      (fun i : Fin (n + 1) ↦ WidePullback.π f i.succ)
      (fun i ↦ WidePullback.π_arrow f i.succ) ≫
        WidePullback.base (fun i : Fin (n + 1) ↦ f i.succ) = WidePullback.π f 0 ≫ f 0 := by
    simp only [WidePullback.lift_base, WidePullback.π_arrow]
  refine ⟨⟨h⟩, ⟨PullbackCone.IsLimit.mk h ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine WidePullback.lift (c.fst ≫ WidePullback.base (fun i : Fin (n + 1) ↦ f i.succ))
      (Fin.cases c.snd (fun i ↦ c.fst ≫ WidePullback.π (fun i : Fin (n + 1) ↦ f i.succ) i)) ?_
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact c.condition.symm
    · simp only [Fin.cases_succ, Category.assoc, WidePullback.π_arrow]
  · intro c
    apply WidePullback.hom_ext
    · intro i
      simp only [Category.assoc, WidePullback.lift_π, Fin.cases_succ]
    · simp only [Category.assoc, WidePullback.lift_base]
  · intro c
    simp only [WidePullback.lift_π, Fin.cases_zero]
  · intro c m hm ht
    apply WidePullback.hom_ext
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [WidePullback.lift_π, Fin.cases_zero] using ht
      · have hc := congrArg (fun l ↦ l ≫ WidePullback.π (fun i : Fin (n + 1) ↦ f i.succ) j) hm
        simpa only [Category.assoc, WidePullback.lift_π, Fin.cases_succ] using hc
    · have hc := congrArg (fun l ↦ l ≫ WidePullback.base (fun i : Fin (n + 1) ↦ f i.succ)) hm
      simpa only [Category.assoc, WidePullback.lift_base] using hc

end SerrePositivity.AlgebraicGeometry
