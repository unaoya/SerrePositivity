module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorComposition

/-!
概要：相対関手空間の前後合成を任意のパラメーター制限後に評価する公式。
方針：fiber の包含への可換式を指定単体と評価点に適用する。
規約：パラメーターの次数と評価先の次数を独立に扱う。
使われ方：二変数の相対 Hom の豊穣自然性の成分計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 相対射の制限後の評価は、相対展開を制限したパラメーターで評価した値。 -/
lemma relativeFunctorUncurry_evaluate {A E B T : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (t : T ⟶ relativeFunctorSpace p a)
    {n m : SimplexCategoryᵒᵖ} (s : T.obj n) (α : n ⟶ m) (x : A.obj m) :
    ((t.app n s).val.app m α) x = (relativeFunctorUncurry t).app m (x, T.map α s) := by
  have h := congrArg (fun z : (relativeFunctorSpace p a).obj m ↦
    (z.val.app m (𝟙 m)) x) (ConcreteCategory.congr_hom (t.naturality α) s)
  change (relativeFunctorUncurry t).app m (x, T.map α s) =
    (t.app n s).val.app m (α ≫ 𝟙 m) x at h
  simpa only [Category.comp_id] using h.symm

/-- 相対合成を任意の制限後に評価すると、同じパラメーターでの二つの評価の合成。 -/
lemma relativeFunctorComposition_apply {B : SSet.{u}} (a b c : Over B)
    {n m : SimplexCategoryᵒᵖ} (f : (relativeFunctorSpace b.hom a.hom).obj n)
    (g : (relativeFunctorSpace c.hom b.hom).obj n) (α : n ⟶ m) (x : a.left.obj m) :
    (((relativeFunctorComposition a b c).app n (f, g)).val.app m α) x =
      (g.val.app m α) (f.val.app m α x) := by
  rw [relativeFunctorUncurry_evaluate, relativeFunctorComposition, relativeFunctorUncurry_curry]
  change (g.val.app m (α ≫ 𝟙 m)) ((f.val.app m (α ≫ 𝟙 m)) x) = _
  simp only [Category.comp_id]

/-- 相対後合成は、任意の制限後にも元の全空間の射への後合成。 -/
lemma relativeFunctorPost_apply {A E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (a : A ⟶ B)
    {n m : SimplexCategoryᵒᵖ} (s : (relativeFunctorSpace p a).obj n)
    (α : n ⟶ m) (x : A.obj m) :
    (((HomotopyLimits.relativeFunctorPost p q f hf a).app n s).val.app m α) x =
      f.app m (s.val.app m α x) := by
  have h := congrArg (fun t ↦ ((t.app n s).app m α) x)
    (HomotopyLimits.relativeFunctorPost_ι p q f hf a)
  exact h

/-- 底上の相対前合成は、任意の制限後にも元の全空間の射への前合成。 -/
lemma relativeFunctorOverPre_apply {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) {n m : SimplexCategoryᵒᵖ}
    (s : (relativeFunctorSpace p b.hom).obj n) (α : n ⟶ m) (x : a.left.obj m) :
    (((relativeFunctorOverPre p f).app n s).val.app m α) x =
      s.val.app m α (f.left.app m x) := by
  have h := congrArg (fun t ↦ ((t.app n s).app m α) x) (relativeFunctorOverPre_ι p f)
  change (((relativeFunctorOverPre p f).app n s).val.app m (α ≫ 𝟙 m)) x =
    s.val.app m (α ≫ 𝟙 m) (f.left.app m x) at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories
