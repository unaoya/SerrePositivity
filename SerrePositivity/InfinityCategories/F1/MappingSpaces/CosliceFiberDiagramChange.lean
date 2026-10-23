module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceIntervalNaturality

/-!
概要：点の図式の表示を変えた coslice fiber の後合成の比較。
方針：等しい図式による fiber の同型を使い、Yoneda の標準表示の自然性へ移す。
規約：変更するのは固定図式の等式による表示だけで、錐の値は保つ。
使われ方：Kerodon Proposition 5.1.6.7、三角形の端点の coslice と右 pinched 写像空間の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：等しい固定図式を用いた終点固定の coslice fiber は同型。
方針：図式の等式から等式の同型を作る。
規約：図式の始域 K と終点 y は保つ。
使われ方：Kerodon Proposition 5.1.6.7、点の標準表示への変更。 -/
def cosliceFiberDiagramIso {K E : SSet.{u}} {a b : K ⟶ E} (h : a = b) (y : E _⦋0⦌) :
    vertexFiber (sliceUnderProjection a) y ≅ vertexFiber (sliceUnderProjection b) y :=
  eqToIso (congrArg (fun e ↦ vertexFiber (sliceUnderProjection e) y) h)

/-- 概要：固定図式の等式による表示変更は展開した錐の族を保つ。
方針：図式の等式で置換し、同型を恒等射へ簡約する。
規約：族のパラメータ A は任意。
使われ方：Kerodon Proposition 5.1.6.7、後合成の二表示の比較。 -/
lemma cosliceFiberDiagramIso_uncurry {A K E : SSet.{u}} {a b : K ⟶ E}
    (h : a = b) (y : E _⦋0⦌) (g : A ⟶ vertexFiber (sliceUnderProjection a) y) :
    sliceUnderUncurry ((g ≫ (cosliceFiberDiagramIso h y).hom) ≫
      vertexFiberι (sliceUnderProjection b) y) =
        sliceUnderUncurry (g ≫ vertexFiberι (sliceUnderProjection a) y) := by
  cases h
  rfl

/-- 概要：標準表示の点の後合成は、通常の coslice の後合成と表示変更の合成。
方針：join の族へ展開し、両者が同じ後合成を行うことを使う。
規約：像の固定点は Yoneda の逆写像により表示する。
使われ方：Kerodon Proposition 5.1.6.7、三角形の射影と模型変更の整合性。 -/
lemma pointCosliceFiberMap_eq_postcomp {E F : SSet.{u}}
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    pointCosliceFiberMap f x y = coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) f y ≫
      (cosliceFiberDiagramIso (SSet.yonedaEquiv_symm_comp x f)
        (f.app (Opposite.op ⦋0⦌) y)).hom := by
  apply cosliceFiberUncurry_injective
  have h := pointCosliceFiberMap_uncurry
    (𝟙 (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)) f
  simp only [Category.id_comp] at h
  rw [h]
  unfold cosliceFiberUncurry
  rw [cosliceFiberDiagramIso_uncurry, coslicePostcompFiberMap_ι,
    sliceUnderUncurry_postcomp, Category.id_comp]

/-- 概要：任意の点の図式の後合成の同値条件は右 pinched 写像空間の同値条件と一致する。
方針：点を Yoneda の標準表示へ戻し、表示の同型と区間模型の比較の同値を使う。
規約：両全空間は quasicategory。
使われ方：Kerodon Proposition 5.1.6.7、cocartesian な三角形による充満忠実性の判定。 -/
lemma coslicePostcompFiberMap_equivalence_iff_pinchedHomMap
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (f : E ⟶ F) (y : E _⦋0⦌) :
    IsQCatEquivalence (coslicePostcompFiberMap a f y) ↔
      IsSimplicialHomotopyEquivalence (pinchedHomMap f (SSet.yonedaEquiv a) y) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
  let e := cosliceFiberDiagramIso (SSet.yonedaEquiv_symm_comp x f)
    (f.app (Opposite.op ⦋0⦌) y)
  have he := (qCatEquivalenceOfIso e).isQCatEquivalence
  have hc : IsQCatEquivalence (coslicePostcompFiberMap (SSet.yonedaEquiv.symm x) f y) ↔
      IsQCatEquivalence (pointCosliceFiberMap f x y) := by
    rw [pointCosliceFiberMap_eq_postcomp]
    exact ⟨fun h ↦ h.comp he, fun h ↦ he.cancel_right h⟩
  rw [Equiv.apply_symm_apply]
  exact hc.trans (pointCosliceFiberMap_equivalence_iff_pinchedHomMap f x y)

end SerrePositivity.InfinityCategories
