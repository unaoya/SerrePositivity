module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceFactorization

/-!
概要：入力付き相対因子化を同じ固定入力の下の全余錐へ戻す。
方針：join 宇宙同型で余錐形状を戻し、反復 coslice 同型を適用する。
規約：元の入力図式と同じ表示添字余錐を厳密に保持する。
使われ方：入力付き相対交互構成の実際の一段延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：形状同型上の全余錐を同じ固定入力の coslice 内へ戻す。
方針：全余錐を形状同型の逆へ制限して既存の反復同型を使う。
規約：入力した余錐の全単体を保持する。
使われ方：固定入力付き一段延長の構成。 -/
def fixedSourceCoconeOfShape {K L M C : SSet.{u}} {a : K ⟶ C}
    (R : L ⟶ sliceUnder a) (e : M ≅ join K L)
    (d : JoinCocone (e.hom ≫ sliceUnderUncurry R)) : JoinCocone R :=
  fixedSourceCocone R ⟨joinMap e.inv (𝟙 Δ[0]) ≫ d.val, by
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, d.property,
      e.inv_hom_id_assoc]⟩

/-- 概要：形状を戻した入力付き余錐の射影は元の全余錐の右制限。
方針：同じ全余錐に対する固定入力の射影等式を使う。
規約：全射の厳密な等式。
使われ方：元の成分表示への制限。 -/
lemma fixedSourceCoconeOfShape_projection {K L M C : SSet.{u}} {a : K ⟶ C}
    (R : L ⟶ sliceUnder a) (e : M ≅ join K L)
    (d : JoinCocone (e.hom ≫ sliceUnderUncurry R)) :
    (fixedSourceCoconeOfShape R e d).val ≫ sliceUnderProjection a =
      joinMap (joinInr K L) (𝟙 Δ[0]) ≫ joinMap e.inv (𝟙 Δ[0]) ≫ d.val := by
  exact fixedSourceCocone_projection R _

/-- 概要：固定入力を保持する相対因子化の余錐。
方針：具体的な相対 slice 余錐を元の固定入力の coslice へ戻す。
規約：指定された因子化データを使う。
使われ方：入力付き閉前置段の全余錐。 -/
def fixedSourceFactorizationCocone
    {J K L I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    {R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z}
    {a : J ⟶ I} {j : J ⟶ L}
    {P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x}
    (t : RelativeComponentFactorization a
      ((SSet.uliftFunctor.{u + 1, u}).map (j ≫ joinInr K L))
      (fixedSourceShapeDiagram R) P) : JoinCocone R :=
  fixedSourceCoconeOfShape R (uliftJoinIso K L)
    (relativeSliceCocone (fixedSourceShapeDiagram R) t.comparison)

/-- 概要：入力付き全余錐を指定成分へ制限すると、同じ表示内の延長余錐を回収する。
方針：全余錐の右制限と成分比較辺の slice 等式を合成する。
規約：入力を保持したまま元の表示添字を延長する。
使われ方：入力付き閉前置段の現在成分条件。 -/
lemma fixedSourceFactorizationCocone_component
    {J K L I : SSet.{u}} {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    {R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z}
    {a : J ⟶ I} {j : J ⟶ L}
    {P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x}
    (t : RelativeComponentFactorization a
      ((SSet.uliftFunctor.{u + 1, u}).map (j ≫ joinInr K L))
      (fixedSourceShapeDiagram R) P) :
    joinMap ((SSet.uliftFunctor.{u + 1, u}).map j) (𝟙 Δ[0]) ≫
        (fixedSourceFactorizationCocone t).val ≫ sliceUnderProjection z =
      (((uliftSliceUnderIso.{u, u + 1} a).hom.app (Opposite.op ⦋0⦌))
        (ULift.up t.index)).val ≫ P := by
  rw [fixedSourceFactorizationCocone, fixedSourceCoconeOfShape_projection]
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
    ← Category.assoc, ← joinMap_comp, Category.id_comp]
  have h : ((SSet.uliftFunctor.{u + 1, u}).map j ≫
      joinInr ((SSet.uliftFunctor.{u + 1, u}).obj K)
        ((SSet.uliftFunctor.{u + 1, u}).obj L)) ≫ (uliftJoinIso K L).inv =
      (SSet.uliftFunctor.{u + 1, u}).map (j ≫ joinInr K L) := by
    rw [Category.assoc, ← uliftJoinIso_inr K L, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, ← CategoryTheory.Functor.map_comp]
  rw [h]
  exact t.component_slice

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
