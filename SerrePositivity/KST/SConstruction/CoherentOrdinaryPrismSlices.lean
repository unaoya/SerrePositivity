module
public import SerrePositivity.KST.SConstruction.CoherentOrdinaryPrism

/-! # 通常積圏表示で元の円柱の両端を回収する
概要：prism の通常積圏表示の各時刻の部分圏を、元の円柱の端点と厳密に同定する。
方針：入力列と定数時刻を分け、元の円柱の端点等式を全単体で用いる。
規約：元の図式の全射と高次単体を保持する。
使われ方：元の K prism の下段と上段の図式・頂点を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 入力圏を、同じ入力と固定時刻の積圏の部分圏へ送る。 -/
def coherentPrismSliceFunctor (I : Type u) [SmallCategory I] (t : ULift.{u} (Fin 2)) :
    I ⥤ I × ULift.{u} (Fin 2) :=
  (𝟭 I).prod' ((CategoryTheory.Functor.const I).obj t)

/-- 下段の全合成列は、元の円柱の時刻零の包含そのもの。 -/
lemma coherentOrdinaryPrismSlice_zero (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (coherentPrismSliceFunctor I (ULift.up 0))) ≫
      (coherentOrdinaryPrismIso.{u, v} I).hom =
      SSet.ι₀ (X := (SSet.uliftFunctor.{v, u}).obj (nerve I)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply ULift.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  · apply SSet.stdSimplex.ext
    intro i
    rfl

/-- 上段の全合成列は、元の円柱の時刻一の包含そのもの。 -/
lemma coherentOrdinaryPrismSlice_one (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (coherentPrismSliceFunctor I (ULift.up 1))) ≫
      (coherentOrdinaryPrismIso.{u, v} I).hom =
      SSet.ι₁ (X := (SSet.uliftFunctor.{v, u}).obj (nerve I)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · apply ULift.ext
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  · apply SSet.stdSimplex.ext
    intro i
    rfl

/-- 下段の全図式は元の円柱の始点図式を厳密に回収する。 -/
lemma coherentOrdinaryPrismSlice_source {I : Type u} [SmallCategory I] {X : SSet.{max u v}}
    {f g : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ X} (H : SSet.Homotopy f g) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (coherentPrismSliceFunctor I (ULift.up 0))) ≫
      ((coherentOrdinaryPrismIso.{u, v} I).hom ≫ H.h) = f := by
  rw [← Category.assoc, coherentOrdinaryPrismSlice_zero, H.h₀]

/-- 上段の全図式は元の円柱の終点図式を厳密に回収する。 -/
lemma coherentOrdinaryPrismSlice_target {I : Type u} [SmallCategory I] {X : SSet.{max u v}}
    {f g : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ X} (H : SSet.Homotopy f g) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (coherentPrismSliceFunctor I (ULift.up 1))) ≫
      ((coherentOrdinaryPrismIso.{u, v} I).hom ≫ H.h) = g := by
  rw [← Category.assoc, coherentOrdinaryPrismSlice_one, H.h₁]

/-- 通常の入力関手による前合成は、元の coherent 図式の頂点対象を保持する。 -/
lemma coherentStringVertexObject_precomp {I J : Type u} [SmallCategory I] [SmallCategory J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (G : J ⥤ I)
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C) (j : J) :
    coherentStringVertexObject ((SSet.uliftFunctor.{v, u}).map (nerveMap G) ≫ Q) j =
      coherentStringVertexObject Q (G.obj j) := by
  have hv : (nerveMap G).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (G.obj j) := ComposableArrows.ext₀ rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (Q.app _ (ULift.up
    ((nerveMap G).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))) = _
  rw [hv]
  rfl

end SerrePositivity.KST.SConstruction
