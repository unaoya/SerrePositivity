module

public import SerrePositivity.InfinityCategories.F2.Ind.AugmentedUniverseReverse
public import SerrePositivity.InfinityCategories.Stable.UniverseJoin
public import SerrePositivity.InfinityCategories.Core.JoinReverse

/-!
概要：join の反転と宇宙持ち上げの比較を全単体の射へ束ねる。
方針：切断表示の可換性を各次数で適用し、順射の同型則から逆射も得る。
規約：全射の等式を保持。使われ方：元の有限余極限余錐の Yoneda 保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- join の順反転と宇宙持ち上げの比較の全正方形。 -/
lemma joinUniverseReverse_hom (K L : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map (stableJoinReverseHom K L) ≫
      (uliftJoinIso L.op K.op).hom ≫
        joinMap (uliftOppositeIso L).hom (uliftOppositeIso K).hom =
    (uliftOppositeIso (join K L)).hom ≫
      SSet.opFunctor.map (uliftJoinIso K L).hom ≫
        stableJoinReverseHom ((SSet.uliftFunctor.{v, u}).obj K)
          ((SSet.uliftFunctor.{v, u}).obj L) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact (augmentedReversePairUp K L (n + 1) (SSet.opObjEquiv s.down)).symm

/-- 同じ全正方形の逆射による表示。 -/
lemma joinUniverseReverse_inv (K L : SSet.{u}) :
    (uliftJoinIso L.op K.op).inv ≫
      (SSet.uliftFunctor.{v, u}).map (stableJoinReverseIso K L).inv ≫
        (uliftOppositeIso (join K L)).hom =
    joinMap (uliftOppositeIso L).hom (uliftOppositeIso K).hom ≫
      (stableJoinReverseIso ((SSet.uliftFunctor.{v, u}).obj K)
        ((SSet.uliftFunctor.{v, u}).obj L)).inv ≫
          SSet.opFunctor.map (uliftJoinIso K L).inv := by
  let a := (SSet.uliftFunctor.{v, u}).mapIso (stableJoinReverseIso K L)
  let b := uliftJoinIso.{u, v} L.op K.op
  let d := stableJoinReverseIso ((SSet.uliftFunctor.{v, u}).obj K)
    ((SSet.uliftFunctor.{v, u}).obj L)
  let e := SSet.opFunctor.mapIso (uliftJoinIso.{u, v} K L)
  have h := joinUniverseReverse_hom.{u, v} K L
  change a.hom ≫ b.hom ≫ _ = _ ≫ e.hom ≫ d.hom at h
  have hh := congrArg (fun f => b.inv ≫ a.inv ≫ f ≫ d.inv ≫ e.inv) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] at hh
  exact hh.symm

end SerrePositivity.InfinityCategories.F2.Ind
