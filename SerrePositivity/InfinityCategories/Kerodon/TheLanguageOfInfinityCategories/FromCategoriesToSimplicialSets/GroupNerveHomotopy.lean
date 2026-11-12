module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
public import Mathlib.Tactic.CrossRefAttribute

/-!
分割で生成：docstring を書き直すこと
概要：群 nerve の連続 Kan 置換の高次ホモトピー消滅。
方針：StrictSegal 性から元の境界定数単体を定数と同定し、Kan 置換単位の逆で全基点へ移す。
規約：KanHomotopy の添字は実次数。群の可換性や有限性は不要。
使われ方：Sp-8 (2)、K-cof が使う n > 1 の消滅。

対応節は Kerodon 1.3（Tag 002L）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 小さな亜群の nerve はホモトピー圏の亜群性から Kan となる。 -/
@[kerodon 0037]
lemma groupoidNerve_kanComplex (D : Type u) [SmallCategory D] [IsGroupoid D] : KanComplex (nerve D) := by
  let e : hoFunctor.obj (nerve D) ≌ D :=
    Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of D))
  have : IsGroupoid (hoFunctor.obj (nerve D)) := isGroupoid_of_reflects_iso e.functor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag.groupoidNerve_kanComplex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.groupoidNerve_kanComplex
