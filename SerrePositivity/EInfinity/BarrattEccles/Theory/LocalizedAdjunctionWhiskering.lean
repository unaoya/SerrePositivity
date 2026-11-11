module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.F1B.Adjunction.Adjunction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestriction

/-!
# 局所化源に沿う quasicategory の二胞体の降下

## 概要
HA §1.3.4 の導来随伴の単位と余単位を、局所化の前合成に沿って降ろす。

## 方針
関手 ∞ 圏の充満忠実性を、双圏の二胞体の全単射へ写す。

## 規約
quasicategory の指定の二胞体を使う。

## 使われ方
Barratt–Eccles の底変更随伴の単位と余単位。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Bicategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

local instance (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 関手 ∞ 圏で充満忠実な前合成は、双圏の二胞体でも全単射。 -/
def qcatPrecompFullyFaithful {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] (q : X ⟶ Y)
    (h : IsFullyFaithful ((pre q).app Z)) :
    (Bicategory.precomp (qcatOf Z) (qcatMap q)).FullyFaithful := by
  let ff := h.toHoFullyFaithful
  have hb (F G : qcatOf Y ⟶ qcatOf Z) : Function.Bijective
      ((Bicategory.precomp (qcatOf Z) (qcatMap q)).map :
        (F ⟶ G) → ((qcatMap q ≫ F) ⟶ (qcatMap q ≫ G))) := by
    let e := (qcatCellEquiv F.hom G.hom).trans
      (ff.homEquiv.trans (qcatCellEquiv (q ≫ F.hom) (q ≫ G.hom)).symm)
    have he (α : F ⟶ G) : e α = qcatMap q ◁ α := by
      apply (qcatCellEquiv (q ≫ F.hom) (q ≫ G.hom)).injective
      change (hoFunctor.map ((pre q).app Z)).toFunctor.map (qcatCellEquiv _ _ α) = _
      exact (qcatCell_whiskerLeft q α).symm
    constructor
    · intro α β hab
      apply e.injective
      rw [he, he]
      exact hab
    · intro β
      obtain ⟨α, ha⟩ := e.surjective β
      exact ⟨α, (he α).symm.trans ha⟩
  letI : (Bicategory.precomp (qcatOf Z) (qcatMap q)).Full := ⟨fun {F G} => (hb F G).2⟩
  letI : (Bicategory.precomp (qcatOf Z) (qcatMap q)).Faithful := ⟨fun {F G} => (hb F G).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful _

end SerrePositivity.EInfinity
