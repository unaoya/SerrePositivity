module
public import SerrePositivity.InfinityCategories.Stable.NestedCoslice

/-! # 二重 coslice の単体集合としての同型

概要：余錐全体の下の coslice と、元の coslice 内で余錐の下の coslice は同型。
方針：任意パラメーターからの射の同値と前合成の自然性を使う。
規約：値域に quasicategory 性を仮定しない。
使われ方：S4 の余極限頂点の付加による制限の trivial Kan fibration 性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二通りの coslice への任意パラメーターからの射は同値。
方針：coslice の普遍性の間に join の組み替えによる図式の同値を挟む。
規約：A は任意の単体集合。使われ方：二重 coslice の比較同型。 -/
def nestedCosliceHomEquiv {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) (A : SSet.{u}) :
    (A ⟶ sliceUnder c.val) ≃
      (A ⟶ sliceUnder (SSet.yonedaEquiv.symm (show (sliceUnder p) _⦋0⦌ from c))) :=
  (sliceUnderEquiv c.val).trans
    ((nestedCosliceDiagramEquiv c A).trans
      (sliceUnderEquiv (SSet.yonedaEquiv.symm (show (sliceUnder p) _⦋0⦌ from c))).symm)

/-- 概要：二重 coslice の射の同値を二度 uncurry すると join の逆同型での前合成になる。
方針：curry・uncurry の逆則を二度使う。
規約：固定条件の証明に依存しない射の等式。
使われ方：比較同値のパラメーターに関する自然性。 -/
lemma nestedCosliceHomEquiv_doubleUncurry {K X A : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p)
    (f : A ⟶ sliceUnder c.val) :
    sliceUnderUncurry (sliceUnderUncurry (nestedCosliceHomEquiv c A f)) =
      (stableJoinAssociator K Δ[0] A).inv ≫ sliceUnderUncurry f := by
  let G := nestedCosliceDiagramCurry c A ((sliceUnderEquiv c.val) f)
  change sliceUnderUncurry (sliceUnderUncurry (sliceUnderCurry G.val G.property)) = _
  rw [sliceUnderUncurry_curry]
  dsimp only [G, nestedCosliceDiagramCurry, sliceUnderEquiv]
  rw [sliceUnderUncurry_curry]
  rfl

/-- 概要：二重 coslice の射の同値はパラメーターの前合成に関して自然。
方針：二度 uncurry し、join の逆結合同型の自然性で比較する。
規約：f と g は任意の単体的な射。使われ方：同値を実際の同型として表す。 -/
lemma nestedCosliceHomEquiv_naturality {K X A B : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (f : A ⟶ B) (g : B ⟶ sliceUnder c.val) :
    nestedCosliceHomEquiv c A (f ≫ g) = f ≫ nestedCosliceHomEquiv c B g := by
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm (show (sliceUnder p) _⦋0⦌ from c))
  apply sliceUnderUncurry_injective p
  rw [nestedCosliceHomEquiv_doubleUncurry,
    sliceUnderUncurry_precomp (nestedCosliceHomEquiv c B g) f,
    sliceUnderUncurry_precomp (sliceUnderUncurry (nestedCosliceHomEquiv c B g))
      (joinMap (𝟙 Δ[0]) f), nestedCosliceHomEquiv_doubleUncurry,
    sliceUnderUncurry_precomp g f]
  have h := stableJoinAssociator_inv_naturality (𝟙 K) (𝟙 (Δ[0] : SSet.{u})) f
  simpa only [joinMap_id, Category.assoc] using
    congrArg (fun e ↦ e ≫ sliceUnderUncurry g) h.symm

/-- 概要：余錐全体の下の coslice は元の coslice 内で余錐の下の coslice と同型。
方針：任意パラメーターからの射の自然な同値を恒等射に適用する。
規約：追加の仮定なし。使われ方：S4 の余極限頂点を忘れる制限の比較。 -/
def nestedCosliceIso {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    sliceUnder c.val ≅ sliceUnder (SSet.yonedaEquiv.symm (show (sliceUnder p) _⦋0⦌ from c)) where
  hom := nestedCosliceHomEquiv c _ (𝟙 _)
  inv := (nestedCosliceHomEquiv c _).symm (𝟙 _)
  hom_inv_id := by
    apply (nestedCosliceHomEquiv c (sliceUnder c.val)).injective
    rw [nestedCosliceHomEquiv_naturality, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := nestedCosliceHomEquiv_naturality c
      ((nestedCosliceHomEquiv c _).symm (𝟙 _)) (𝟙 (sliceUnder c.val))
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm

end SerrePositivity.InfinityCategories
