module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ExtOne

/-!
概要：通常の錐の脚を join の一次単体で表示する。
方針：一次単体の三つの切断を境界と混合辺に分ける。
規約：元の錐の頂点と脚を指定したまま比較する。
使われ方：B5 の Under の標準錐の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：点と nerve の join で頂点から指定対象へ出る一次単体。
方針：join の切断による場合分けと射列の一次元の外延性を使う。
規約：同じ宇宙で元の圏・図式・錐を保持する。
使われ方：B5 の標準錐の古典比較。 -/
def coneLegSimplex {I : Type u} [Category.{u} I] (i : I) :
    (join (Δ[0] : SSet.{u}) (nerve I)) _⦋1⦌ :=
  Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
    (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) (nerveVertex i)

/-- 概要：join から nerve への射は両端と全ての脚で決まる。
方針：join の切断による場合分けと射列の一次元の外延性を使う。
規約：同じ宇宙で元の圏・図式・錐を保持する。
使われ方：B5 の標準錐の古典比較。 -/
lemma nerve_joinPoint_hom_ext {I C : Type u} [Category.{u} I] [Category.{u} C]
    {f g : join (Δ[0] : SSet.{u}) (nerve I) ⟶ nerve C}
    (h₀ : joinInl (Δ[0] : SSet.{u}) (nerve I) ≫ f = joinInl _ _ ≫ g)
    (h₁ : joinInr (Δ[0] : SSet.{u}) (nerve I) ≫ f = joinInr _ _ ≫ g)
    (he : ∀ i : I, f.app (Opposite.op ⦋1⦌) (coneLegSimplex i) =
      g.app _ (coneLegSimplex i)) : f = g := by
  apply SerrePositivity.InfinityCategories.F1B.nerve_hom_ext_one
  rintro ⟨l, a, b⟩
  fin_cases l
  · cases a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ (Opposite.op ⦋1⦌)) b
  · change (Δ[0] : SSet.{u}) _⦋0⦌ at a
    change (nerve I) _⦋0⦌ at b
    have ha : a = stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    subst a
    obtain ⟨i, rfl⟩ := (nerveEquiv (C := I)).symm.surjective b
    exact he i
  · cases b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀ (Opposite.op ⦋1⦌)) a

/-- 概要：二点の join の混合辺は標準区間の恒等一次単体に写る。
方針：join の切断による場合分けと射列の一次元の外延性を使う。
規約：同じ宇宙で元の圏・図式・錐を保持する。
使われ方：B5 の標準錐の古典比較。 -/
lemma pointJoinStdSimplexIso_zero_leg : (pointJoinStdSimplexIso.{u} 0).hom.app (Opposite.op ⦋1⦌)
    (Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) =
        stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  rw [pointJoinStdSimplexIso_hom_app_val]
  fin_cases i <;> rfl

/-- 概要：通常の錐の脚は nerve へ移した錐の混合辺に一致する。
方針：join の切断による場合分けと射列の一次元の外延性を使う。
規約：同じ宇宙で元の圏・図式・錐を保持する。
使われ方：B5 の標準錐の古典比較。 -/
lemma nerveCone_leg {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (x : Cone F) (i : I) :
    (SerrePositivity.InfinityCategories.F1B.nerveCone x).val.app (Opposite.op ⦋1⦌) (coneLegSimplex i) =
      ComposableArrows.mk₁ (x.π.app i) := by
  change HomotopyLimits.initialJoinChain (coneLegSimplex i) ⋙
    SerrePositivity.InfinityCategories.F1B.coneWithInitialFunctor x = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories.F1B
