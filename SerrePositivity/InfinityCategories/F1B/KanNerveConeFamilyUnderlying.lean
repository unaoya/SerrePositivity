module

public import SerrePositivity.InfinityCategories.F1B.KanConeExtensionFunctor
public import SerrePositivity.InfinityCategories.F1B.KanNerveFunctorVertex
public import SerrePositivity.InfinityCategories.F1B.KanNerveFunctorHomCategory
public import SerrePositivity.InfinityCategories.Core.ConeFamily

/-!
概要：錐の nerve を join の形の関手単体集合へ写し固定図式を照合する。
方針：指数比較と前合成の自然性を使う。
規約：比較射の構成と普遍性の証明を区別する。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：通常の定値関手の nerve は元の頂点への定値な射。
方針：合成可能射列への両方の作用を比較する。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanNerveMap_const (A : Type u) [Category.{u} A] (x : C) :
    nerveMap ((Functor.const A).obj x) = SSet.const (nerveVertex x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：通常の錐の nerve を join の形の関手単体集合へ写す。
方針：拡張関手の指数比較と join の同型による前合成を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
def kanNerveConeFamilyUnderlying : nerve (Cone F) ⟶
    (ihom (join (Δ[0] : SSet.{u}) (nerve I))).obj (nerve C) :=
  nerveMap (kanConeExtensionFunctor (F := F)) ≫
    (kanNerveFunctorCategoryIso (WithInitial I) C).hom ≫
      (pre (HomotopyLimits.initialJoinNerveIso I).hom).app (nerve C)

/-- 概要：関手単体集合への比較射は元の図式を全ての単体で固定する。
方針：指数比較の前合成の自然性と通常の制限の式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanNerveConeFamilyUnderlying_fixed : kanNerveConeFamilyUnderlying (F := F) ≫
    coneRestriction (nerve I) (nerve C) = SSet.const (functorVertex (nerveMap F)) := by
  have hp : (pre (HomotopyLimits.initialJoinNerveIso I).hom).app (nerve C) ≫
      (pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app (nerve C) =
        (pre (nerveMap (WithInitial.incl : I ⥤ WithInitial I))).app (nerve C) := by
    rw [← NatTrans.comp_app, ← pre_map]
    have he := HomotopyLimits.joinInr_initialJoinNerveMap I
    change joinInr (Δ[0] : SSet.{u}) (nerve I) ≫
      (HomotopyLimits.initialJoinNerveIso I).hom = _ at he
    rw [he]
  dsimp only [kanNerveConeFamilyUnderlying, coneRestriction]
  simp only [Category.assoc]
  rw [hp]
  rw [← kanNerveFunctorCategoryIso_precomp (WithInitial.incl : I ⥤ WithInitial I)]
  change nerveMap (kanConeExtensionFunctor (F := F) ⋙
    (Functor.whiskeringLeft I (WithInitial I) C).obj WithInitial.incl) ≫
      (kanNerveFunctorCategoryIso I C).hom = _
  rw [kanConeExtensionFunctor_restrict, kanNerveMap_const, SSet.const_comp]
  change SSet.const ((kanNerveFunctorCategoryIso I C).hom.app _
    (ComposableArrows.mk₀ F)) = _
  rw [kanNerveFunctorCategoryIso_vertex]

/-- 概要：比較射の関手頂点は元の指定された join の錐を表す。
方針：関手頂点の指数比較の公式を使う。
規約：同じ宇宙で元の指定図式を保持する。
使われ方：B5 の局所錐と普遍性の古典比較。 -/
lemma kanNerveConeFamilyUnderlying_vertex (c : Cone F) :
    (kanNerveConeFamilyUnderlying (F := F)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c) =
      functorVertex (kanNerveCone c).val := by
  simp only [kanNerveConeFamilyUnderlying, NatTrans.comp_app_apply, nerveMap_app_mk₀]
  change ((pre (HomotopyLimits.initialJoinNerveIso I).hom).app (nerve C)).app
    (Opposite.op ⦋0⦌) ((kanNerveFunctorCategoryIso (WithInitial I) C).hom.app _
      (ComposableArrows.mk₀ (kanConeWithInitialFunctor c))) = _
  rw [kanNerveFunctorCategoryIso_vertex (kanConeWithInitialFunctor c)]
  rfl

end SerrePositivity.InfinityCategories.F1B
