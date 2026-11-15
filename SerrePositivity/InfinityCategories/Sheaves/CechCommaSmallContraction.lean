module

public import SerrePositivity.InfinityCategories.Sheaves.CechCommaContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleContractionCospan
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：Čech comma の収縮を対象・射の共通の宇宙の模型へ運ぶ。
方針：AsSmall の同じ up/down を用い、元の二自然変換を持ち上げる。
使われ方：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）と §3.2（Tag 00V2）。
規約：元の comma の対象と射の宇宙を同一視せず、持ち上げを明示する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 元の comma のサイズを明示した同じ模型。 -/
abbrev CechCommaSmall (d : CategoryTheory.CechNerveData U) (V : C) :=
  AsSmall.{max u v w} (CechComma d V)

/-- 収縮関手を同じ小さい模型へ移す。 -/
def cechCommaSmallPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    CechCommaSmall.{u, v, w} d V ⥤ CechCommaSmall.{u, v, w} d V :=
  AsSmall.down ⋙ cechCommaPrefix d r ⋙ AsSmall.up

/-- 元の恒等から prefix への変換を持ち上げる。 -/
def cechCommaSmallToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    𝟭 (CechCommaSmall.{u, v, w} d V) ⟶ cechCommaSmallPrefix d r where
  app a := ULift.up ((cechCommaToPrefix d r).app (AsSmall.down.obj a))
  naturality {a b} f := by
    apply ULift.ext
    exact (cechCommaToPrefix d r).naturality (AsSmall.down.map f)

/-- 根から prefix への同じ変換を持ち上げる。 -/
def cechCommaSmallRootToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    (Functor.const (CechCommaSmall.{u, v, w} d V)).obj (AsSmall.up.obj (cechCommaRoot d r)) ⟶
      cechCommaSmallPrefix d r where
  app a := ULift.up ((cechCommaRootToPrefix d r).app (AsSmall.down.obj a))
  naturality {a b} f := by
    apply ULift.ext
    exact (cechCommaRootToPrefix d r).naturality (AsSmall.down.map f)

/-- 指定根があれば、同じ小さい comma の nerve は弱可縮。 -/
lemma cechCommaSmall_isWeaklyContractible (d : CategoryTheory.CechNerveData U)
    (r : V ⟶ U) : IsWeaklyContractible (nerve (CechCommaSmall.{u, v, w} d V)) :=
  nerve_isWeaklyContractible_of_contractionCospan (AsSmall.up.obj (cechCommaRoot d r))
    (cechCommaSmallPrefix d r) (cechCommaSmallToPrefix d r) (cechCommaSmallRootToPrefix d r)

end SerrePositivity.InfinityCategories.Sheaves
