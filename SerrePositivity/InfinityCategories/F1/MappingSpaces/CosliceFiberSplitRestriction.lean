module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberDiagramChange
public import SerrePositivity.InfinityCategories.Stable.CosliceRestriction

/-!
概要：右 anodyne な切断を持つ形の崩壊は、固定終点の coslice fiber の比較同値を与える。
方針：切断への制限は自明 Kan fibration で、崩壊への制限との合成は図式を正規化すると恒等。
規約：形の崩壊自体を圏同値と仮定せず、実際の錐の制限写像の同値性を結論する。
使われ方：左の固定単体を変えた写像空間の比較と、twisted arrow の対角模型への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 任意の族について、固定終点の coslice 制限は join の左因子での前合成そのもの。 -/
lemma cosliceRestrictionFiberMap_uncurry {A K L C : SSet.{u}}
    (p : K ⟶ C) (f : L ⟶ K) (y : C _⦋0⦌)
    (g : A ⟶ vertexFiber (sliceUnderProjection p) y) :
    sliceUnderUncurry ((g ≫ cosliceRestrictionFiberMap p f y) ≫
      vertexFiberι (sliceUnderProjection (f ≫ p)) y) =
    joinMap f (𝟙 A) ≫ sliceUnderUncurry (g ≫ vertexFiberι (sliceUnderProjection p) y) := by
  rw [Category.assoc, cosliceRestrictionFiberMap, vertexFiberMap_ι, ← Category.assoc,
    sliceUnderUncurry_restrict]

/-- 崩壊とその切断への実際の制限を合成し、固定図式の表示を戻すと恒等となる。 -/
lemma cosliceRestrictionFiberMap_split_comp {A C : SSet.{u}} (x y : C _⦋0⦌)
    (f : A ⟶ (Δ[0] : SSet.{u})) (v : (Δ[0] : SSet.{u}) ⟶ A)
    (hvf : v ≫ f = 𝟙 _) :
    cosliceRestrictionFiberMap (SSet.yonedaEquiv.symm x) f y ≫
      (cosliceRestrictionFiberMap (f ≫ SSet.yonedaEquiv.symm x) v y ≫
        (cosliceFiberDiagramIso (by rw [← Category.assoc, hvf, Category.id_comp]) y).hom) =
          𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) := by
  apply cosliceFiberUncurry_injective x y
  unfold cosliceFiberUncurry
  rw [← Category.assoc]
  rw [cosliceFiberDiagramIso_uncurry]
  rw [cosliceRestrictionFiberMap_uncurry]
  have h := cosliceRestrictionFiberMap_uncurry (SSet.yonedaEquiv.symm x) f y
    (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))
  simp only [Category.id_comp] at h ⊢
  rw [h, ← Category.assoc, ← joinMap_comp, hvf, Category.id_comp, joinMap_id, Category.id_comp]

/-- 右 anodyne な切断を持つ崩壊への制限は、元の固定終点の写像空間で同値。 -/
lemma cosliceRestrictionFiberMap_isQCatEquivalence_of_rightAnodyne_section
    {A C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)
    (f : A ⟶ (Δ[0] : SSet.{u})) (v : (Δ[0] : SSet.{u}) ⟶ A) [Mono v]
    (hv : rightAnodyneExtensions v) (hvf : v ≫ f = 𝟙 _) :
    IsQCatEquivalence (cosliceRestrictionFiberMap (SSet.yonedaEquiv.symm x) f y) := by
  have ht := sliceUnderRestrict_trivialKanFibration (f ≫ SSet.yonedaEquiv.symm x) v hv
  have : TrivialKanFibration
      (cosliceRestrictionFiberMap (f ≫ SSet.yonedaEquiv.symm x) v y) :=
    cosliceRestrictionFiberMap_trivialKanFibration _ _ _
  let h : v ≫ (f ≫ SSet.yonedaEquiv.symm x) = SSet.yonedaEquiv.symm x := by
    rw [← Category.assoc, hvf, Category.id_comp]
  let e := cosliceFiberDiagramIso h y
  have hr := (isQCatEquivalence_of_trivialKanFibration
    (cosliceRestrictionFiberMap (f ≫ SSet.yonedaEquiv.symm x) v y)).comp
      (qCatEquivalenceOfIso e).isQCatEquivalence
  have hi := (qCatEquivalenceOfIso
    (Iso.refl (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))).isQCatEquivalence
  change IsQCatEquivalence (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)) at hi
  rw [← cosliceRestrictionFiberMap_split_comp x y f v hvf] at hi
  exact hr.cancel_right hi

end SerrePositivity.InfinityCategories
