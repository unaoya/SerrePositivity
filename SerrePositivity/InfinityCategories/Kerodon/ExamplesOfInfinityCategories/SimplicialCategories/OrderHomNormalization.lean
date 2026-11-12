module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomConstantTransport

/-!
概要：同じ対象へ正規化した Hom の等式を、元の対象間の等式へ戻す。
方針：対象の等号の合成と、通常の順序図式の定値 Hom を使う。
規約：対象の正規化を変えても、元の Hom 作用は変えない。
使われ方：第一三角形の六つの順向きラベル対における Hom の照合。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 両側の Hom を同じ二対象へ正規化して照合すれば、元の Hom の等式が得られる。 -/
lemma simplicialHom_eq_of_normalized
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {T : SSet.{u}}
    {A B A' B' X Y : C} (p : T ⟶ SimplicialCategory.sHom A B)
    (q : T ⟶ SimplicialCategory.sHom A' B') (ha : A = A') (hb : B = B')
    (hA : A = X) (hB : B = Y) (hA' : A' = X) (hB' : B' = Y)
    (h : p ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) =
      q ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB')) :
    p ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) = q := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB'))).mp
  simpa only [Category.assoc, eqToHom_trans] using h

/-- 添字を制限した通常の順序図式の Hom を、元のラベルの対象へ正規化する。 -/
lemma orderDiagramEnrichedHom_reindex_normalized
    {J K : Type u} [LinearOrder J] [LinearOrder K]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (α : J →o K) (D : K ⥤ C) (i j : SimplicialThickening J) (hij : i.as ≤ j.as)
    {a b : K} (ha : α i.as = a) (hb : α j.as = b) (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom (α.toFunctor ⋙ D) i j ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (congrArg D.obj ha) (congrArg D.obj hb)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (D.map f)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom_const _ i j hij, SSet.const_comp]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHomVertex_transport (congrArg D.obj ha) (congrArg D.obj hb)]
  congr 2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.functor_map_transport_of_isThin D ha hb (α.toFunctor.map (homOfLE hij)) f

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
