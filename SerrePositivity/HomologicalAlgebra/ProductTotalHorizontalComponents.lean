module
public import SerrePositivity.HomologicalAlgebra.ProductTotalFirstRow

/-!
概要：非有界積全複体への横ホモトピーの次数成分。
方針：元の成分射影の後に内側の鎖写像を合成して、同じ積へ持ち上げる。
規約：横次数を一つ下げる。次数が合わない成分は零で、有界性を仮定しない。
使われ方：HA 1.2.4、G10 の重みの鎖ホモトピー比較の積 Tot への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits Preadditive HomologicalComplex
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]
variable {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)}

/-- 横次数を一つ下げる同じ鎖写像の族から作る積全複体の成分。 -/
def horizontalComponent (H : ∀ a : ℤ, K.X (a+1) ⟶ L.X a) (n m : ℤ) :
    ((functor C).obj K).X n ⟶ ((functor C).obj L).X m :=
  lift L m (fun a b _ => πOrZero K (a+1) b n ≫ (H a).f b)

/-- 同じ元の射影への制限は、横次数を下げる指定射の成分。 -/
@[reassoc (attr := simp)]
theorem horizontalComponent_π (H : ∀ a : ℤ, K.X (a+1) ⟶ L.X a)
    (a b n m : ℤ) (hab : a+b=m) :
    horizontalComponent H n m ≫ π L a b m hab =
      πOrZero K (a+1) b n ≫ (H a).f b := lift_π _ _ _ _ _ _

/-- 全次数が一つ下がらないときには、同じ成分は零。 -/
theorem horizontalComponent_shape (H : ∀ a : ℤ, K.X (a+1) ⟶ L.X a)
    (n m : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel m n) : horizontalComponent H n m = 0 := by
  apply hom_ext L m
  intro a b hab
  rw [horizontalComponent_π, zero_comp, πOrZero_eq_zero K (a+1) b n, zero_comp]
  change ¬ (m+1=n) at h
  omega

end SerrePositivity.HomologicalAlgebra.ProductTotal
