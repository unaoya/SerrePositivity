module

public import SerrePositivity.InfinityCategories.F2.Ind.JoinUniverseReverse
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteYonedaOppositeLimits
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexConeReindex

/-!
概要：同じ元の余錐の反転と宇宙持ち上げの全射を照合する。
方針：join の宇宙比較と順逆反転の自然性を合成する。
規約：全錐を保持。使われ方：native な Yoneda 有限余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 同じ元の余錐の反転と持ち上げは形状同型による制限の後で全射が一致。 -/
lemma uliftCoconeReverse_val {K X : SSet.{u}} {D : K ⟶ X} (c : JoinCocone D) :
    (mapJoinCone (uliftOppositeIso X).hom
      (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))).val =
    (restrictJoinCone (SerrePositivity.InfinityCategories.F1B.coconeReverseCone (JoinCocone.ulift.{u, u + 1} c))
      (uliftOppositeIso K).hom).val := by
  change ((uliftConeShapeIso K.op 0).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c).val) ≫
      (uliftOppositeIso X).hom =
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (uliftOppositeIso K).hom ≫
      (SerrePositivity.InfinityCategories.F1B.coconeReverseCone (JoinCocone.ulift.{u, u + 1} c)).val
  rw [SerrePositivity.InfinityCategories.F1B.coconeReverseCone_val, SerrePositivity.InfinityCategories.F1B.coconeReverseCone_val]
  have hval : (JoinCocone.ulift.{u, u + 1} c).val =
      (uliftCoconeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map c.val := rfl
  rw [hval]
  simp only [Functor.map_comp, Category.assoc]
  have hn : (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map c.val) ≫
      (uliftOppositeIso X).hom =
    (uliftOppositeIso (join K (Δ[0] : SSet.{u}))).hom ≫
      SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map c.val) := rfl
  rw [hn]
  unfold uliftConeShapeIso uliftCoconeShapeIso
  simp only [Iso.trans_inv, joinIso, Iso.refl_inv, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (uliftJoinIso (Δ[0] : SSet.{u}) K.op).inv,
    ← uliftJoinIso_inv_naturality]
  simp only [Category.assoc]
  have hi := congrArg (fun f => f ≫ SSet.opFunctor.map
    ((SSet.uliftFunctor.{u + 1, u}).map c.val))
      (joinUniverseReverse_inv.{u, u + 1} K (Δ[0] : SSet.{u}))
  simp only [Category.assoc] at hi
  rw [hi]
  have hr := stableJoinReverse_inv_naturality
    (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj K)) (uliftStdSimplexIso.{u, u + 1} 0).inv
  have hh := congrArg (fun f => f ≫ SSet.opFunctor.map (uliftJoinIso.{u, u + 1} K Δ[0]).inv ≫
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map c.val)) hr
  simp only [Category.assoc] at hh
  rw [← hh]
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
