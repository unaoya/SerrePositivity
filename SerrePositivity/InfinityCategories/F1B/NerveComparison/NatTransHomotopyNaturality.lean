module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransHomotopy
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransWhiskering

/-!
概要：通常の自然変換と指定錐の後合成を実際のホモトピーへ移す。
方針：nerve の指数比較の辺を uncurry して成分を計算する。
規約：元の図式と自然変換を保ち、可逆性を仮定しない。
使われ方：B5 の指定単位・余単位の局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}


/-- 概要：ホモトピー表示は通常の後合成と厳密に可換。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_whiskerRight {E : Type u} [Category.{u} E] (η : F ⟶ G) (H : D ⥤ E) :
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy η).h ≫ nerveMap H =
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (Functor.whiskerRight η H)).h := by
  change uncurry (SSet.yonedaEquiv.symm (SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge η).edge) ≫ nerveMap H =
    uncurry (SSet.yonedaEquiv.symm (SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge (Functor.whiskerRight η H)).edge)
  rw [← uncurry_natural_right, SSet.yonedaEquiv_symm_comp]
  congr 2
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_postcomp H) (Opposite.op ⦋1⦌)) (ComposableArrows.mk₁ η)
  simp only [NatTrans.comp_app_apply, nerveMap_app_mk₁] at h
  exact h.symm

/-- 概要：ホモトピー表示は通常の前合成と厳密に可換。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_whiskerLeft {A : Type u} [Category.{u} A] (I : A ⥤ C) (η : F ⟶ G) :
    (nerveMap I ▷ (Δ[1] : SSet.{u})) ≫ (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy η).h =
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (Functor.whiskerLeft I η)).h := by
  change (nerveMap I ▷ (Δ[1] : SSet.{u})) ≫
    uncurry (SSet.yonedaEquiv.symm (SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge η).edge) =
      uncurry (SSet.yonedaEquiv.symm (SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge (Functor.whiskerLeft I η)).edge)
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  congr 2
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_precomp I) (Opposite.op ⦋1⦌)) (ComposableArrows.mk₁ η)
  simp only [NatTrans.comp_app_apply, nerveMap_app_mk₁] at h
  exact h.symm


/-- 概要：恒等変換の辺は恒等辺に等しい。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransEdge_id (F : C ⥤ D) :
    SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge (𝟙 F) = Edge.id (functorVertex (nerveMap F)) := by
  apply Edge.ext
  change ((nerve.edgeMk (𝟙 F)).map (SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso C D).hom).edge = _
  rw [nerve.edgeMk_id, Edge.map_id]
  change (Edge.id ((SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso C D).hom.app _ (ComposableArrows.mk₀ F))).edge = _
  rw [SerrePositivity.InfinityCategories.F1B.nerveFunctorCategoryIso_vertex]

/-- 概要：恒等変換のホモトピーは時間に定値。
方針：指定された辺の指数比較と自然性を使う。
規約：同じ宇宙の小さい圏と元の指定変換を扱う。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_id (F : C ⥤ D) :
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (𝟙 F)).h = fst (nerve C) (Δ[1] : SSet.{u}) ≫ nerveMap F := by
  change uncurry (SSet.yonedaEquiv.symm (SerrePositivity.InfinityCategories.F1B.nerveNatTransEdge (𝟙 F)).edge) = _
  rw [nerveNatTransEdge_id]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  dsimp [SSet.Truncated.Edge.id, SSet.Edge.id, functorVertex, uncurry]
  rfl

end SerrePositivity.InfinityCategories.F1B
