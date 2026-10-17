module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMonomorphismLifting

/-!
# 中断した任意モデル源への一般化：NerveDiagramExtension

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative coherent lifting for general inverse-inverting nerve value diagrams。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0470][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0470
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative coherent lifting for general inverse-inverting nerve value diagrams

The values can depend on both endpoints or the entire chain. Only their
inverse maps and component right lifting properties are used.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveDiagramExtension
variable {D : Type uD} [Category.{vD} D]

abbrev InvertsInverse (A : Index D ⥤ SSet.{v}) := ∀ {s t : Index D} (f : s ⟶ t),
  NerveCoherentFamily.inverse D f → IsIso (A.map f)

abbrev System (A : Index D ⥤ SSet.{v}) := NerveCoherentFamily.simplices.{vD, uD, v} D ⟶ A
abbrev LowerSystem (A : Index D ⥤ SSet.{v}) (n : ℕ) :=
  lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ NerveCoherentFamily.simplices.{vD, uD, v} D ⟶
    lowerInclusion (NerveCoherentFamily.reedy D) n ⋙ A

variable (A B : Index D ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : InvertsInverse A) (hB : InvertsInverse B)
  (hp : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s))

include hA hB hp in
lemma localLifting : ∀ s, HasLiftingProperty
    (relativeLatchingMap (NerveCoherentFamily.reedy D) s
      (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)))
    (relativeMatchingMap (NerveCoherentFamily.reedy D) s p) :=
  fun s => (SimplexMonomorphismLifting.reedyRight (nerve D) A B p hA hB hp s) _
    (NerveMonomorphismLifting.parameter_mono (D := D) s)

variable (target : System B) (n : ℕ) (old : LowerSystem A n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) p =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) target)

lemma square : CommSq (initial.to A)
    (initial.to (NerveCoherentFamily.simplices.{vD, uD, v} D)) p target :=
  ⟨initialIsInitial.hom_ext _ _⟩

def below : LiftBelow (NerveCoherentFamily.reedy D) (square A B p target) n where
  hom := old
  fac_left := by
    apply NatTrans.ext
    funext s
    exact (initialIsInitial.isInitialObj
      ((evaluation (Index D) SSet.{v}).obj s.obj) (⊥_ (Index D ⥤ SSet.{v}))).hom_ext _ _
  fac_right := hboundary

/-- Retain the entire target system and every specified old component in a general value diagram. -/
def extend : System A := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.lift (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_boundary : extend A B p hA hB hp target n old hboundary ≫ p = target := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.fac_right (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_restrict : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend A B p hA hB hp target n old hboundary) = old := by
  let := localLifting A B p hA hB hp
  exact RelativeLifting.restrict (NerveCoherentFamily.reedy D) (square A B p target) n
    (below A B p target n old hboundary)

lemma extend_component (s : Lower (NerveCoherentFamily.reedy D) n) :
    (extend A B p hA hB hp target n old hboundary).app s.obj = old.app s :=
  congr_app (extend_restrict A B p hA hB hp target n old hboundary) s

end SerrePositivity.SimplicialModel.NerveDiagramExtension
