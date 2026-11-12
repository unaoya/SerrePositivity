module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：正規化した定値 Hom 作用を、同じ通常の射の対象移送と両立させる。
方針：対象の等号を消去して単位・合成則へ帰着する。
規約：充填性は不要で、全パラメーターの射の等式を保持する。
使われ方：第一三角形の各ラベルで、計算済みの Hom を指定射列の Hom と同定する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 対象の移送は、同じ通常の射の豊穣頂点を対応する共役射の頂点に送る。 -/
lemma simplicialHomVertex_transport
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B A' B' : C} (ha : A = A') (hb : B = B') (f : A ⟶ B) :
    (eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' A B f) =
      SimplicialCategory.homEquiv' A' B' (eqToHom ha.symm ≫ f ≫ eqToHom hb) := by
  subst A'
  subst B'
  simp

/-- 計算済みの定値 Hom の正規化を、同じ通常の射の対象移送に続ける。 -/
lemma simplicialHom_constant_transport
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {T : SSet.{u}}
    {A₀ B₀ A B A' B' : C} (p : T ⟶ SimplicialCategory.sHom A₀ B₀)
    (hA : A₀ = A) (hB : B₀ = B) (f : A ⟶ B)
    (h : p ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) =
      SSet.const (SimplicialCategory.homEquiv' A B f))
    (ha : A = A') (hb : B = B') (f' : A' ⟶ B')
    (hf : eqToHom ha.symm ≫ f ≫ eqToHom hb = f') :
    p ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans ha) (hB.trans hb)) =
      SSet.const (SimplicialCategory.homEquiv' A' B' f') := by
  have he : eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans ha) (hB.trans hb)) =
      eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) := by
    cases hA; cases hB; cases ha; cases hb
    simp
  rw [he, ← Category.assoc, h, SSet.const_comp, simplicialHomVertex_transport ha hb f, hf]

/-- 通常の順序図式の Hom は、指定された同じ順序射の頂点への定値射。 -/
lemma orderDiagramEnrichedHom_const
    {J : Type u} [LinearOrder J] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (D : J ⥤ C) (i j : SimplicialThickening J) (hij : i.as ≤ j.as) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom D i j =
      SSet.const (SimplicialCategory.homEquiv' _ _ (D.map (homOfLE hij))) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  rfl

/-- 薄い底の射を対象の等号で移送すると、同じ二対象間の指定射の像になる。 -/
lemma functor_map_transport_of_isThin
    {I : Type w} [Category I] [Quiver.IsThin I] {C : Type v} [Category C]
    (D : I ⥤ C) {a b a' b' : I} (ha : a = a') (hb : b = b')
    (f : a ⟶ b) (f' : a' ⟶ b') :
    eqToHom (congrArg D.obj ha).symm ≫ D.map f ≫ eqToHom (congrArg D.obj hb) =
      D.map f' := by
  subst a'
  subst b'
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id]
    using congrArg D.map (Subsingleton.elim f f')

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
