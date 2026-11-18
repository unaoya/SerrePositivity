module

public import SerrePositivity.InfinityCategories.Sheaves.CechCommaContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleContractionCospan
public import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
概要：大きい通常圏の Čech comma の既存収縮を、Hom と同じ小さい宇宙で使う。
方針：comma の対象は単体圏の添字と一つの Hom だけを持つので、同じ Hom 宇宙で包む。
規約：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の既存の宇宙移送の法則。
使われ方：集合値の Čech 解消の各点での収縮。元の prefix と二自然変換を再利用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 単体圏の添字と Hom からなる元の comma を、Hom と同じ小さい宇宙に包む。 -/
abbrev CechCommaLocal (d : CategoryTheory.CechNerveData U) (V : C) : Type v :=
  AsSmall.{v} (CechComma d V)

/-- 元の同じ prefix を小さい comma の表示へ移す。 -/
def cechCommaLocalPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    CechCommaLocal d V ⥤ CechCommaLocal d V :=
  AsSmall.down ⋙ cechCommaPrefix d r ⋙ AsSmall.up

/-- 恒等から同じ prefix への元の自然変換を包む。 -/
def cechCommaLocalToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    𝟭 (CechCommaLocal d V) ⟶ cechCommaLocalPrefix d r where
  app a := ULift.up ((cechCommaToPrefix d r).app (AsSmall.down.obj a))
  naturality {a b} f := by
    apply ULift.ext
    exact (cechCommaToPrefix d r).naturality (AsSmall.down.map f)

/-- 同じ根から prefix への元の自然変換を包む。 -/
def cechCommaLocalRootToPrefix (d : CategoryTheory.CechNerveData U) (r : V ⟶ U) :
    (Functor.const (CechCommaLocal d V)).obj (AsSmall.up.obj (cechCommaRoot d r)) ⟶
      cechCommaLocalPrefix d r where
  app a := ULift.up ((cechCommaRootToPrefix d r).app (AsSmall.down.obj a))
  naturality {a b} f := by
    apply ULift.ext
    exact (cechCommaRootToPrefix d r).naturality (AsSmall.down.map f)

/-- 根を一本与えると、Hom の小さい宇宙での同じ comma は弱可縮。 -/
lemma cechCommaLocal_isWeaklyContractible (d : CategoryTheory.CechNerveData U)
    (r : V ⟶ U) : IsWeaklyContractible (nerve (CechCommaLocal d V)) :=
  nerve_isWeaklyContractible_of_contractionCospan (AsSmall.up.obj (cechCommaRoot d r))
    (cechCommaLocalPrefix d r) (cechCommaLocalToPrefix d r) (cechCommaLocalRootToPrefix d r)

end SerrePositivity.InfinityCategories.Sheaves
