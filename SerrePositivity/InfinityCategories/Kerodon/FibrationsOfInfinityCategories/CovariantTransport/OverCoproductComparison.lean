module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrecompositionOverColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：Over 圏の coproduct 上の自然な比較の同値条件。
方針：coproduct を初期対象からの wide pushout として表示して比較を貼る。
規約：各枝の構造射は異なってよく、終域だけを共通に固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各次元の標準単体と境界の族。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：Over 圏の cofan を初期対象からの wide pushout の cocone にする。
方針：各 cofan の包含と初期対象からの一意な射を使う。
規約：族の添字は宇宙 u。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの族の比較。 -/
noncomputable def overCoproductWideCocone {J : Type u} {S : SSet.{u}}
    (objs : J → Over S) (c : Cofan objs) :
    Cocone (WidePushoutShape.wideSpan (⊥_ (Over S)) objs (fun j ↦ initial.to (objs j))) :=
  WidePushoutShape.mkCocone (initial.to c.pt) (fun j ↦ c.inj j)
    (fun _ ↦ initialIsInitial.hom_ext _ _)

/-- 概要：Over 圏の coproduct の cofan は初期対象からの wide pushout の余極限を与える。
方針：枝の射を cofan から貼り、初期対象の脚の等式を一意性で補う。
規約：空の族も含む。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、任意のセルの族の貼り合わせ。 -/
noncomputable def overCoproductWideCocone_isColimit {J : Type u} {S : SSet.{u}}
    (objs : J → Over S) (c : Cofan objs) (hc : IsColimit c) :
    IsColimit (overCoproductWideCocone objs c) where
  desc s := hc.desc (Cofan.mk s.pt (fun j ↦ s.ι.app (some j)))
  fac s j := by
    cases j with
    | none => exact initialIsInitial.hom_ext _ _
    | some j => exact hc.fac (Cofan.mk s.pt (fun j ↦ s.ι.app (some j))) ⟨j⟩
  uniq s m hm := by
    apply hc.hom_ext
    rintro ⟨j⟩
    exact (hm (some j)).trans (hc.fac (Cofan.mk s.pt (fun j ↦ s.ι.app (some j))) ⟨j⟩).symm

/-- 概要：初期対象と族の各対象で自然な比較が同値条件を満たせば coproduct でも満たす。
方針：初期対象からの wide pushout の比較の貼り合わせを使う。
規約：二つの関手は単射と指定した wide pushout を保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、構造射を保ったセルの族への拡張。 -/
lemma isPrecompositionEquivalence_over_of_coproduct_cocone
    (J : Type u) {S : SSet.{u}} {F G : Over S ⥤ SSet.{u}} (t : F ⟶ G)
    [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape (WidePushoutShape J) F]
    [PreservesColimitsOfShape (WidePushoutShape J) G]
    (objs : J → Over S) (c : Cofan objs) (hc : IsColimit c)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (⊥_ (Over S))))
    (h : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app (objs j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (t.app c.pt) := by
  let D := WidePushoutShape.wideSpan (⊥_ (Over S)) objs (fun j ↦ initial.to (objs j))
  have hI : IsInitial ((⊥_ (Over S)).left) :=
    IsInitial.isInitialObj (Over.forget S) _ initialIsInitial
  have : ∀ j, Mono (D.map (.init j)) := by
    intro j
    have : Mono (D.map (.init j)).left := hI.mono_from _
    exact Over.mono_of_mono_left _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_of_widePushout_colimit J t D
    (overCoproductWideCocone objs c) (overCoproductWideCocone_isColimit objs c hc)
  rintro (_ | j)
  · exact h0
  · exact h j

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
