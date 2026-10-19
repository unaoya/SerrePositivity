module

public import SerrePositivity.InfinityCategories.F1B.KanNerveConeFiberFamilyIso
public import SerrePositivity.InfinityCategories.F1B.KanNerveFunctorFiberIso
public import SerrePositivity.InfinityCategories.F1B.KanNerveQCatEquivalence
public import SerrePositivity.InfinityCategories.Core.LimitConeFamily

/-!
概要：通常の錐と native な錐の族の比較を構成する。
方針：指数比較と固定図式上の fiber の同型を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所極限の双方向比較。
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

/-- 概要：指定比較射を錐の同値と fiber の同型の合成として表示する。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma kanNerveConeFamilyMap_factorization : nerveMap (kanConeFiberFunctor (F := F)) ≫
    (kanNerveFunctorFiberIso (kanConeRestrictionFunctor (I := I) (C := C)) F).hom ≫
      (kanNerveConeFiberFamilyIso (F := F)).hom = kanNerveConeFamilyMap (F := F) := by
  apply vertexFiber_hom_ext (coneRestriction (nerve I) (nerve C)) (functorVertex (nerveMap F))
  simp only [Category.assoc]
  rw [kanNerveConeFiberFamilyIso_inclusion]
  rw [← Category.assoc (kanNerveFunctorFiberIso _ _).hom,
    kanNerveFunctorFiberIso_hom_inclusion]
  change nerveMap (kanConeFiberFunctor (F := F)) ≫
    (nerveMap (Functor.Fiber.fiberInclusion) ≫ (kanNerveConeExtensionIso (I := I) (C := C)).hom) =
      kanNerveConeFamilyUnderlying
  rfl
/-- 概要：通常の錐の nerve と native な錐の族の比較は同値。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma kanNerveConeFamilyMap_isQCatEquivalence :
    IsQCatEquivalence (kanNerveConeFamilyMap (F := F)) := by
  have h := (kanNerveMap_isQCatEquivalence (kanConeFiberFunctor (F := F))).comp
    (qCatEquivalenceOfIso (kanNerveFunctorFiberIso (kanConeRestrictionFunctor (I := I) (C := C)) F)
      |>.isQCatEquivalence)
  have h' :=
    h.comp (qCatEquivalenceOfIso (kanNerveConeFiberFamilyIso (F := F)) |>.isQCatEquivalence)
  change IsQCatEquivalence ((nerveMap (kanConeFiberFunctor (F := F)) ≫
    (kanNerveFunctorFiberIso (kanConeRestrictionFunctor (I := I) (C := C)) F).hom) ≫
      (kanNerveConeFiberFamilyIso (F := F)).hom) at h'
  rwa [Category.assoc, kanNerveConeFamilyMap_factorization] at h'
/-- 概要：native な極限性を通常の錐の nerve の終対象性と比較する。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma kanNerveCone_isLimit_iff_terminal (c : Cone F) :
    IsLimitCone (kanNerveCone c) ↔ IsTerminalVertex (nerveVertex c) := by
  rw [isLimitCone_iff_isTerminalVertex_coneFamily]
  have h :=
    (kanNerveConeFamilyMap_isQCatEquivalence (F := F)).choose.isTerminalVertex_iff (nerveVertex c)
  change IsTerminalVertex (nerveVertex c) ↔
    IsTerminalVertex ((kanNerveConeFamilyMap (F := F)).app _ (nerveVertex c)) at h
  change IsTerminalVertex (nerveVertex c) ↔
    IsTerminalVertex ((kanNerveConeFamilyMap (F := F)).app _ (ComposableArrows.mk₀ c)) at h
  rw [kanNerveConeFamilyMap_vertex] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F1B
