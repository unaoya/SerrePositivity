module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EnrichedAdjunctionHomComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.AdjunctionHomLimits

/-!
概要：豊穣随伴の合成互換データを、既存の終域に自然な Hom 同型へ接続する。
方針：元の通常の射への Hom 作用を全次数で評価し、同じ随伴の零単体へ戻す。
規約：モデル圏の条件は不要。使われ方：既存の strict 極限保存と混合辺の比較の共通入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] (R : EnrichedFunctor SSet.{u} D C)
variable {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
variable (e : EnrichedAdjunctionHomComposition R adj)

/-- 豊穣関手の元の通常の射への作用は、同じ豊穣 Hom 写像との後合成。 -/
lemma enrichedUnderlyingMap_eHom {Y Z : D} (g : Y ⟶ Z) :
    eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor R).map g) =
      eHomEquiv SSet g ≫ R.map Y Z := by
  apply (SSet.unitHomEquiv _).injective
  exact coherentEnrichedUnderlyingFunctor_vertex R g

/-- 豊穣合成互換は通常の終域の射への全単体での自然性を与える。 -/
lemma enrichedAdjunctionHom_postcompose (X : C) {Y Z : D} (g : Y ⟶ Z) :
    eHomWhiskerLeft SSet (L.obj X) g ≫ (e.homIso X Z).hom =
      (e.homIso X Y).hom ≫ eHomWhiskerLeft SSet X
        ((coherentEnrichedUnderlyingFunctor R).map g) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋n⦌)
    (s, (eHomEquiv SSet (C := D) g).app (Opposite.op ⦋n⦌) PUnit.unit)) (e.hom_comp X Y Z)
  have hg := congrArg (fun k ↦ k.app (Opposite.op ⦋n⦌) PUnit.unit)
    (enrichedUnderlyingMap_eHom R g)
  change (eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor R).map g)).app _ PUnit.unit =
    (R.map Y Z).app _ ((eHomEquiv SSet g).app _ PUnit.unit) at hg
  change (e.homIso X Z).hom.app _ ((eComp SSet (L.obj X) Y Z).app _
    (s, (eHomEquiv SSet g).app _ PUnit.unit)) =
      (eComp SSet X (R.obj Y) (R.obj Z)).app _
        ((e.homIso X Y).hom.app _ s,
          (R.map Y Z).app _ ((eHomEquiv SSet g).app _ PUnit.unit)) at h
  change (e.homIso X Z).hom.app _ ((eComp SSet (L.obj X) Y Z).app _
    (s, (eHomEquiv SSet g).app _ PUnit.unit)) =
      (eComp SSet X (R.obj Y) (R.obj Z)).app _
        ((e.homIso X Y).hom.app _ s,
          (eHomEquiv SSet ((coherentEnrichedUnderlyingFunctor R).map g)).app _ PUnit.unit)
  rw [hg]
  exact h

/-- 元の通常随伴の零単体を保持して、既存の自然な Hom 同型の界面へ移す。 -/
def enrichedAdjunctionHom_toSimplicial : SimplicialAdjunctionHomIso adj :=
  ⟨fun X ↦ NatIso.ofComponents (fun Y ↦ e.homIso X Y)
    (fun g ↦ enrichedAdjunctionHom_postcompose R adj e X g),
    fun X Y f ↦ congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) PUnit.unit) (e.hom_zero X Y f)⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
