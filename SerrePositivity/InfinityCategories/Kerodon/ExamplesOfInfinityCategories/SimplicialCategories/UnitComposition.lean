module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDegeneracy

/-!
# 単位を含む合成の保存

概要：単位を保つ Hom 写像は同じ端点を含む二項合成を自動的に保つ。
方針：同じ端点の Path の列を恒等列と同定し、行き先の豊穣単位則を評価する。
規約：他の Hom 写像の合成則は仮定しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の退化した三対象での合成則。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type v} [LinearOrder J]
variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：始点の単位 Hom を保つ写像は左の区間が一点の合成を保つ。
方針：一点区間の列を恒等列へ移し、行き先の左単位則を各次数で評価する。
規約：もう一つの Hom 写像は任意でよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の同じ始点を持つ三対象での検査。 -/
lemma pathHom_comp_left_unit (a b : J) (A B : C)
    (l : nerve (Path a a) ⟶ SimplicialCategory.sHom A A)
    (f : nerve (Path a b) ⟶ SimplicialCategory.sHom A B)
    (hl : eId SSet (SimplicialThickening.mk a) ≫ l = eId SSet A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a a b ≫ f = (l ⊗ₘ f) ≫ SimplicialCategory.sHomComp A A B := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  have hp : p = (eId SSet (SimplicialThickening.mk a)).app m PUnit.unit :=
    CategoryTheory.Functor.ext (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLoop_eq_id a (p.obj t))
  subst p
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a a b).app m
      ((eId SSet (SimplicialThickening.mk a)).app m PUnit.unit, q) = q :=
    CategoryTheory.Functor.ext (fun t ↦
      @Category.id_comp (SimplicialThickening J) _ (.mk a) (.mk b) (q.obj t))
  have hlm := congrArg (fun k ↦ k.app m PUnit.unit) hl
  change l.app m ((eId SSet (SimplicialThickening.mk a)).app m PUnit.unit) =
    (eId SSet A).app m PUnit.unit at hlm
  have ht := congrArg (fun k ↦ k.app m (f.app m q)) (e_id_comp SSet A B)
  change f.app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a a b).app m
    ((eId SSet (SimplicialThickening.mk a)).app m PUnit.unit, q)) =
    (SimplicialCategory.sHomComp A A B).app m
      (l.app m ((eId SSet (SimplicialThickening.mk a)).app m PUnit.unit), f.app m q)
  rw [hs, hlm]
  exact ht.symm

/-- 概要：終点の単位 Hom を保つ写像は右の区間が一点の合成を保つ。
方針：一点区間の列を恒等列へ移し、行き先の右単位則を各次数で評価する。
規約：もう一つの Hom 写像は任意でよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の同じ終点を持つ三対象での検査。 -/
lemma pathHom_comp_right_unit (a b : J) (A B : C)
    (f : nerve (Path a b) ⟶ SimplicialCategory.sHom A B)
    (r : nerve (Path b b) ⟶ SimplicialCategory.sHom B B)
    (hr : eId SSet (SimplicialThickening.mk b) ≫ r = eId SSet B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b b ≫ f = (f ⊗ₘ r) ≫ SimplicialCategory.sHomComp A B B := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  have hq : q = (eId SSet (SimplicialThickening.mk b)).app m PUnit.unit :=
    CategoryTheory.Functor.ext (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathLoop_eq_id b (q.obj t))
  subst q
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b b).app m
      (p, (eId SSet (SimplicialThickening.mk b)).app m PUnit.unit) = p :=
    CategoryTheory.Functor.ext (fun t ↦
      @Category.comp_id (SimplicialThickening J) _ (.mk a) (.mk b) (p.obj t))
  have hrm := congrArg (fun k ↦ k.app m PUnit.unit) hr
  change r.app m ((eId SSet (SimplicialThickening.mk b)).app m PUnit.unit) =
    (eId SSet B).app m PUnit.unit at hrm
  have ht := congrArg (fun k ↦ k.app m (f.app m p)) (e_comp_id SSet A B)
  change f.app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap a b b).app m
    (p, (eId SSet (SimplicialThickening.mk b)).app m PUnit.unit)) =
    (SimplicialCategory.sHomComp A B B).app m
      (f.app m p, r.app m ((eId SSet (SimplicialThickening.mk b)).app m PUnit.unit))
  rw [hs, hrm]
  exact ht.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
