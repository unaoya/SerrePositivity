module
public import Mathlib.CategoryTheory.Grothendieck
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve

/-!
概要：元のweighted nerveの係数から、同じGrothendieck射列の対象と射を回収する。
方針：各prefixの最終対象と、元の係数の自然性からの型の移送を使う。
規約：IS-W2 R03eの逆向きの単体の部分。新しいfiber対象や脚は選ばない。
使われ方：同じ厳密な比較同型の逆射と両往復の検査。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (s : weightedNerveSimplex (F ⋙ nerveFunctor) n)

/-- 元の各重み係数の、同じfiberの通常の射列によるYoneda表示。 -/
def grothWeightedNerveFiberChain (i : Fin (n+1)) : ComposableArrows (F.obj (s.1.obj i)) i.val :=
  (SSet.yonedaEquiv (X := nerve (F.obj (s.1.obj i))) (n := SimplexCategory.mk i.val)) (s.2.app i)

/-- 元の係数の全自然性は、同じfiber射列の全初区間への制限の等式。 -/
theorem grothWeightedNerveFiberChain_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
      grothWeightedNerveFiberChain F s j =
        grothWeightedNerveFiberChain F s i ⋙ (F.map (s.1.map f)).toFunctor := by
  have hn := s.2.naturality f
  change stdSimplex.map (simplexPrefixInclusion i.val j.val (leOfHom f)) ≫ s.2.app j =
    s.2.app i ≫ nerveMap (F.map (s.1.map f)).toFunctor at hn
  have hc := congrArg (fun a : stdSimplex.obj (SimplexCategory.mk i.val) ⟶
      nerve (F.obj (s.1.obj j)) =>
    (SSet.yonedaEquiv (X := nerve (F.obj (s.1.obj j))) (n := SimplexCategory.mk i.val)) a) hn
  rw [← SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_comp] at hc
  exact hc

/-- 元の各prefixの最終対象を、元の基底の同じGrothendieck対象にする。 -/
def grothWeightedNerveInverseObj (i : Fin (n+1)) : Grothendieck F :=
  ⟨s.1.obj i, (grothWeightedNerveFiberChain F s i).obj (Fin.last i.val)⟩

/-- 同じ最終頂点の、より長いprefixへの包含の添字。 -/
def grothWeightedNerveInverseIndex {i j : Fin (n+1)} (f : i ⟶ j) : Fin (j.val+1) :=
  ⟨i.val, Nat.lt_succ_of_le (leOfHom f)⟩

/-- 元の係数の自然性が与える、同じfiber射の始域の型の移送。 -/
theorem grothWeightedNerveInverse_source {i j : Fin (n+1)} (f : i ⟶ j) :
    (F.map (s.1.map f)).toFunctor.obj (grothWeightedNerveInverseObj F s i).fiber =
      (grothWeightedNerveFiberChain F s j).obj (grothWeightedNerveInverseIndex f) :=
  (CategoryTheory.Functor.congr_obj (grothWeightedNerveFiberChain_naturality F s f) (Fin.last i.val)).symm

/-- 元のprefixの実射を、同じ基底の射を持つGrothendieck射に戻す。 -/
def grothWeightedNerveInverseMap {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedNerveInverseObj F s i ⟶ grothWeightedNerveInverseObj F s j where
  base := s.1.map f
  fiber := eqToHom (grothWeightedNerveInverse_source F s f) ≫
    (grothWeightedNerveFiberChain F s j).map (homOfLE
      (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from
        Nat.le_of_lt_succ (grothWeightedNerveInverseIndex f).isLt))

/-- 逆向きの射も、元の同じ基底の射を厳密に保つ。 -/
theorem grothWeightedNerveInverseMap_base {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedNerveInverseMap F s f).base = s.1.map f := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
