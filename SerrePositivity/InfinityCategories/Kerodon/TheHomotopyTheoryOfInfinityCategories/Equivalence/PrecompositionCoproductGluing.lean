module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionWideGluing
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
概要：初期対象を共有する任意の族での自然な比較の貼り合わせ。
方針：coproduct を初期対象からの wide pushout として表す。
規約：関手は連結な wide pushout と単射を保つことを要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各次数のセルの族。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：初期対象からの wide pushout の coproduct を点とする cocone。
方針：各対象の coproduct 包含を使う。
規約：添字の宇宙は単体の宇宙 u。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの族の貼り合わせ。 -/
noncomputable def coproductWideCocone {J : Type u} (A : SSet.{u}) (hA : IsInitial A)
    (objs : J → SSet.{u}) : Cocone (WidePushoutShape.wideSpan A objs (fun j ↦ hA.to (objs j))) :=
  WidePushoutShape.mkCocone (hA.to (∐ objs)) (fun j ↦ Sigma.ι objs j)
    (fun _ ↦ hA.hom_ext _ _)

/-- 概要：初期対象からの wide pushout は対象の族の coproduct になる。
方針：各枝の射を coproduct から貼り、共通部分の等式は初期性で確認する。
規約：空の族も含む。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の任意のセルの族。 -/
noncomputable def coproductWideCocone_isColimit {J : Type u}
    (A : SSet.{u}) (hA : IsInitial A) (objs : J → SSet.{u}) :
    IsColimit (coproductWideCocone A hA objs) where
  desc c := Sigma.desc (fun j ↦ c.ι.app (some j))
  fac c j := by
    cases j with
    | none => exact hA.hom_ext _ _
    | some j => exact Sigma.ι_comp_desc _ _
  uniq c m hm := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    exact hm (some j)

/-- 概要：初期対象と族の各対象で自然な比較が同値条件を満たせば coproduct でも満たす。
方針：初期対象からの wide pushout に自然な比較の貼り合わせを適用する。
規約：二つの関手は単射と指定した wide pushout の余極限を保つ。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各次元のセルの族。 -/
lemma isPrecompositionEquivalence_of_coproduct_colimit
    (J : Type u) {F G : SSet.{u} ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F] [PreservesColimitsOfShape (WidePushoutShape J) G]
    (objs : J → SSet.{u}) (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (⊥_ SSet.{u})))
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (objs j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (∐ objs)) := by
  let A : SSet.{u} := ⊥_ SSet.{u}
  let hA : IsInitial A := initialIsInitial
  let D := WidePushoutShape.wideSpan A objs (fun j ↦ hA.to (objs j))
  have : ∀ j, Mono (D.map (.init j)) := fun j ↦ hA.mono_from _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_widePushout_colimit J t D
    (coproductWideCocone A hA objs) (coproductWideCocone_isColimit A hA objs)
  rintro (_ | j)
  · exact h0
  · exact h j

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
