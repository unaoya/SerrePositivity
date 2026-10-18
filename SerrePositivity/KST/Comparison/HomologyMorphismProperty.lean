module

public import SerrePositivity.KST.Comparison.HomologyFilteredColimits
public import SerrePositivity.KST.Comparison.HomologyPushout
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# 整数ホモロジー同型の閉性

概要：整数ホモロジー同型の余極限・余積・retract に関する閉性を証明する。
方針：実際のホモロジー関手が送る同型の逆像として射の性質を定義する。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル濾過を Mathlib の射の性質の API へ接続する。
使われ方：anodyne map の整数ホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：全次数の整数ホモロジーで同型になる単体写像の性質。
方針：各次数の実際のホモロジー関手による同型の逆像の交わりを取る。
規約：IntegralHomologyIsomorphism と同じ条件。
使われ方：余極限や retract に対する閉性。
-/
abbrev integralHomologyEquivalences : MorphismProperty SSet.{u} :=
  ⨅ n : ℕ, (MorphismProperty.isomorphisms AddCommGrpCat.{u}).inverseImage
    (integralHomologyFunctor n)

/--
概要：射の性質による整数ホモロジー同型と既存の条件は同値である。
方針：交わりと逆像の定義を展開する。
規約：追加の数学的条件はない。
使われ方：閉性の API から通常の主張への変換。
-/
theorem integralHomologyEquivalences_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    integralHomologyEquivalences f ↔ IntegralHomologyIsomorphism f := by
  simp only [integralHomologyEquivalences, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage, MorphismProperty.isomorphisms, IntegralHomologyIsomorphism]

/--
概要：整数ホモロジー同型は恒等射を含み合成で閉じる。
方針：同型の逆像と交わりの一般的な閉性を使う。
規約：実際のホモロジー関手の関手性。
使われ方：超限合成の閉性。
-/
instance integralHomologyEquivalences_isMultiplicative :
    integralHomologyEquivalences.{u}.IsMultiplicative := by
  dsimp only [integralHomologyEquivalences]
  infer_instance

/--
概要：整数ホモロジー同型は両側の同型による共役で保たれる。
方針：同型の逆像と交わりの一般的な閉性を使う。
規約：圏論的同型との整合。
使われ方：余積や超限合成の界面。
-/
instance integralHomologyEquivalences_respectsIso :
    integralHomologyEquivalences.{u}.RespectsIso := by
  dsimp only [integralHomologyEquivalences]
  infer_instance

/--
概要：整数ホモロジー同型は retract で閉じる。
方針：各次数のホモロジーで同型の retract となることを使う。
規約：射の圏の retract。
使われ方：小対象構成による anodyne map の記述。
-/
instance integralHomologyEquivalences_stableRetracts :
    integralHomologyEquivalences.{u}.IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    rw [integralHomologyEquivalences_iff] at hg ⊢
    intro n
    exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms AddCommGrpCat)
      (h.map (integralHomologyFunctor n)) (hg n)

/--
概要：整数ホモロジーの全関手が保存する形の余極限ではホモロジー同型が保存される。
方針：保存された余極限余錐に同型の余極限閉性を適用する。
規約：各次数の保存性は構成済みの関手に対する条件。
使われ方：filtered colimit と余積の共通の閉性。
-/
instance integralHomologyEquivalences_stableColimits {J : Type*} [Category* J]
    [∀ n : ℕ, PreservesColimitsOfShape J (integralHomologyFunctor.{u} n)] :
    integralHomologyEquivalences.{u}.IsStableUnderColimitsOfShape J where
  condition F G cF cG hcF hcG α hα f hf := by
    rw [integralHomologyEquivalences_iff]
    intro n
    let H := integralHomologyFunctor.{u} n
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := MorphismProperty.isomorphisms AddCommGrpCat.{u})
      (F ⋙ H) (G ⋙ H) (H.mapCocone cF) (H.mapCocone cG)
      (isColimitOfPreserves H hcF) (isColimitOfPreserves H hcG)
      (Functor.whiskerRight α H)
      (fun j => (integralHomologyEquivalences_iff _).mp (hα j) n)
      (H.map f) (fun j => by
        have h : H.map (cF.ι.app j) ≫ H.map f =
            H.map (α.app j) ≫ H.map (cG.ι.app j) := by
          rw [← H.map_comp, ← H.map_comp, hf j]
        exact h)

/--
概要：整数ホモロジーは指定宇宙の余積を保存する。
方針：AB4 による離散圏の余極限の完全性を適用する。
規約：添字の型と係数の宇宙は一致する。
使われ方：全ての horn を同時に添付する余積。
-/
instance integralHomology_preservesCoproductsOfShape (J : Type u) (n : ℕ) :
    PreservesColimitsOfShape (Discrete J) (integralHomologyFunctor.{u} n) := by
  exact integralHomology_preservesExactColimits n

/--
概要：整数ホモロジー同型は指定宇宙の全ての余積で閉じる。
方針：ホモロジー関手の余積保存を一般の余極限閉性へ適用する。
規約：無限の添字集合も含む。
使われ方：horn 生成射の族の余積。
-/
instance integralHomologyEquivalences_stableCoproducts :
    MorphismProperty.IsStableUnderCoproducts.{u} integralHomologyEquivalences.{u} where

/--
概要：整数ホモロジー同型は filtered colimit で閉じる。
方針：AB5 で証明した全次数の余極限保存を使う。
規約：添字と射の宇宙は単体集合の値宇宙。
使われ方：超限合成の閉性。
-/
instance integralHomologyEquivalences_stableFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u} integralHomologyEquivalences.{u} where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

end SerrePositivity.KST.Comparison
