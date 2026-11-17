module

public import SerrePositivity.AlgebraicGeometry.CechFilteredAugmentedExact
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLiftNaturality
public import SerrePositivity.AlgebraicGeometry.CechAdditiveCoefficientComparison
public import SerrePositivity.AlgebraicGeometry.CechCoefficientExactness
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Final

/-!
概要：任意の宇宙の整数加群で、同じ増大 Čech の完全性を自然数順極限へ渡す。
方針：既存の ULift ℤ の係数移送、AsSmall の同値と各項の加法的比較を使う。
規約：元の各項の加法群と微分を変更しない。
使われ方：実際の構造層の Frobenius 系の増大完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {ι : Type} [DecidableEq ι] [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ有限被覆の整数係数の増大完全性は、任意の宇宙で自然数順極限へ移る。 -/
theorem fullCechIntSequential_augmentedExact
    (D : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ)
    (h : ∀ n, Function.Injective (fullCechDifferential (D.obj n) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential (D.obj n) k)
        (fullCechDifferential (D.obj n) (k + 1))) :
    Function.Injective (fullCechDifferential (colimit D) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential (colimit D) k)
        (fullCechDifferential (colimit D) (k + 1)) := by
  let L := projectiveIntCechLiftFunctor.{u} (ι := ι)
  let eJ : AsSmall.{u} ℕ ⥤ ℕ := (AsSmall.equiv : ℕ ≌ AsSmall.{u} ℕ).symm.functor
  letI : IsFiltered (AsSmall.{u} ℕ) :=
    IsFiltered.of_equivalence (AsSmall.equiv : ℕ ≌ AsSmall.{u} ℕ)
  let DL := eJ ⋙ D ⋙ L
  have hL (j : AsSmall.{u} ℕ) :
      Function.Injective (fullCechDifferential (DL.obj j) 0) ∧
        ∀ k, Function.Exact (fullCechDifferential (DL.obj j) k)
          (fullCechDifferential (DL.obj j) (k + 1)) := by
    let E := D.obj (eJ.obj j)
    let e : ∀ T, E.obj T ≃+ (L.obj E).obj T := fun _ ↦ AddEquiv.refl _
    have he : ∀ {T S : Finset ι} (hTS : T ⊆ S) (x : E.obj T),
        e S ((E.map (homOfLE hTS)).hom x) =
          ((L.obj E).map (homOfLE hTS)).hom (e T x) := by intros; rfl
    exact ⟨fullCechAdditiveCoefficientEquiv_zero_injective E (L.obj E) e he
      (h (eJ.obj j)).1, fun k ↦ fullCechAdditiveCoefficientEquiv_exact E (L.obj E) e he k
        ((h (eJ.obj j)).2 k)⟩
  let e : L.obj (colimit D) ≅ colimit DL :=
    preservesColimitIso L D ≪≫ (Functor.Final.colimitIso eJ (D ⋙ L)).symm
  have hz : Function.Injective (fullCechDifferential (L.obj (colimit D)) 0) :=
    fullCechCoefficientEquiv_zero_injective e.symm
      (fullCechFiltered_injective_zero DL (fun j ↦ (hL j).1))
  have he (k : ℕ) : Function.Exact (fullCechDifferential (L.obj (colimit D)) k)
      (fullCechDifferential (L.obj (colimit D)) (k + 1)) :=
    fullCechCoefficientEquiv_exact e.symm k
      (fullCechFiltered_exact DL k (fun j ↦ (hL j).2 k))
  let a : ∀ T, (L.obj (colimit D)).obj T ≃+ (colimit D).obj T := fun _ ↦ AddEquiv.refl _
  have ha : ∀ {T S : Finset ι} (hTS : T ⊆ S) (x : (L.obj (colimit D)).obj T),
      a S (((L.obj (colimit D)).map (homOfLE hTS)).hom x) =
        ((colimit D).map (homOfLE hTS)).hom (a T x) := by intros; rfl
  exact ⟨fullCechAdditiveCoefficientEquiv_zero_injective (L.obj (colimit D)) (colimit D) a ha hz,
    fun k ↦ fullCechAdditiveCoefficientEquiv_exact (L.obj (colimit D)) (colimit D) a ha k (he k)⟩

end SerrePositivity.AlgebraicGeometry
