module

public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomPostInnerFibration
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseRelativeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomCartesianFibration

/-!
概要：全空間の相対比較の標的の底への射影は inner fibration。
方針：後合成の inner fibration 性を引き戻し、全図式の底への射影へ合成する。
規約：この段階で cartesian fibration 性は主張しない。
使われ方：相対比較の標的の quasicategory 性と底方向の輸送の前提。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対比較の標的の底射影は後合成の充填性から inner fibration となる。
方針：第二射影の引き戻しによる充填性と全図式の射影の充填性を合成する。
規約：添字間の射に単射性は不要。
使われ方：全空間の相対標的を底上の ∞ 圏として扱う。 -/
lemma kanFiberwiseRelativeProjection_innerFibration {C D E : SSet.{u}}
    [Quasicategory E] {K L : Over C} (i : K ⟶ L)
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      IsPrecompositionEquivalence m → HasLiftingProperty m U) :
    InnerFibration (kanFiberwiseRelativeProjection i U) := by
  have : InnerFibration (kanFiberwiseHomPostcomp K.hom U) :=
    kanFiberwiseHomPostcomp_innerFibration K.hom U hU
  have : InnerFibration (pullback.snd (kanFiberwiseHomPostcomp K.hom U)
      (kanFiberwiseHomPre (D := E) i)) :=
    ⟨innerFibrations.pullback_snd _ _ (InnerFibration.mem (q := kanFiberwiseHomPostcomp K.hom U))⟩
  rw [kanFiberwiseRelativeProjection_snd]
  exact ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q :=
    pullback.snd (kanFiberwiseHomPostcomp K.hom U) (kanFiberwiseHomPre (D := E) i)))
      (InnerFibration.mem (q := kanFiberwiseHomProjection L.hom E))⟩

/-- 概要：関手の制限を標的の射とする相対比較の標的は底への inner fibration を持つ。
方針：単射な前合成同値の関手の制限に対する持ち上げ性を適用する。
規約：底 C の quasicategory 性は不要。
使われ方：写像空間の制限定理に用いる境界固定の族。 -/
instance kanFiberwiseRelativeProjection_pre_innerFibration {C P Q X : SSet.{u}}
    [Quasicategory X] {K L : Over C} (i : K ⟶ L)
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] (v : P ⟶ Q) [Mono v] :
    InnerFibration (kanFiberwiseRelativeProjection i ((pre v).app X)) := by
  apply kanFiberwiseRelativeProjection_innerFibration
  intro Y Z m hm he
  have : Mono m := hm
  exact he.hasLiftingProperty_pre v X

/-- 概要：境界固定を含む相対比較の標的は底が ∞ 圏なら ∞ 圏。
方針：標的の底射影の inner fibration 性で内ホーンを持ち上げる。
規約：任意の単射 v に適用する。
使われ方：相対的な輸送の cartesian 辺の比較。 -/
instance kanFiberwiseRelativeTarget_pre_quasicategory {C P Q X : SSet.{u}}
    [Quasicategory C] [Quasicategory X] {K L : Over C} (i : K ⟶ L)
    [CocartesianFibration K.hom] [CocartesianFibration L.hom] (v : P ⟶ Q) [Mono v] :
    Quasicategory (KanFiberwiseRelativeTarget i ((pre v).app X)) :=
  quasicategory_of_innerFibration (kanFiberwiseRelativeProjection i ((pre v).app X))

end SerrePositivity.InfinityCategories.F1B
