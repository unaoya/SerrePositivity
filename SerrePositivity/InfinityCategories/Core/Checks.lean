module

public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：通常の圏の nerve でホモトピー圏の橋を具体化する。
方針：A1a の比較と、nerve 随伴の可逆な余単位を合成する。
規約：圏の対象・射は同じ宇宙に置く。
使われ方：HTT §1.2.3、Kerodon Example 1.4.5.4 の通常の圏との整合性確認。
-/

@[expose] public section

universe u

open CategoryTheory SSet SSet.Truncated

namespace SerrePositivity.InfinityCategories

/-- 概要：通常の小さい圏の nerve の辺のホモトピー圏は元の圏と同値。
方針：比較同値と Mathlib の nerve 随伴の余単位を合成する。
規約：`C : Type u` と `[Category.{u} C]` のみを仮定する。
使われ方：HTT §1.2.3、Kerodon Example 1.4.5.4 の具体例。 -/
noncomputable def nerveHomotopyCategoryEquivalence (C : Type u) [Category.{u} C] :
    HomotopyCategory₂ ((truncation 2).obj (nerve C)) ≌ C :=
  (homotopyCategoryBridge (nerve C)).trans
    (Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of C)))

/-- 概要：nerve の射に対応する辺の類は比較によって同じ辺の道の類に移る。
方針：商写像の代表元で定義を計算する。
規約：元の圏の射 `f : x ⟶ y` の向きを保持する。
使われ方：HTT §1.2.3、Kerodon Example 1.4.5.4 の辺での整合性。 -/
lemma nerveBridge_map_edge {C : Type u} [Category.{u} C] {x y : C} (f : x ⟶ y) :
    (homotopyCategoryBridge (nerve C)).functor.map
      (HomotopyCategory₂.homMk (CategoryTheory.nerve.edgeMk f).toTruncated) =
        SSet.HomotopyCategory.homMk (CategoryTheory.nerve.edgeMk f) :=
  rfl

end SerrePositivity.InfinityCategories
