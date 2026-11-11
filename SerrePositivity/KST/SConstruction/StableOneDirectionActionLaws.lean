module
public import SerrePositivity.KST.SConstruction.StableOneDirectionRealization
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedActionLaws

/-!
概要：一次方向実現の全自然同値族の単位・合成を同じ次数で回収する。
方針：全対角を展開せず、各次数の元の core 関手の法則を評価する。
規約：全入力単体を保持する。使われ方：元の一次方向商の点つき関手化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants

/-- 概要：元の全作用は豊穣単位を保存する。
方針：同じ次数の core 関手の単位則を使う。
規約：元の作用の等式。使われ方：同じ商作用の単位則。 -/
lemma stableOneDirectionAction_unit (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (𝟙 ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C)) ⊗ₘ
      eId SSet.{u} C) ≫ stableOneDirectionAction r C C =
        (ρ_ ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C))).hom := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  let G := (stableMultiSCoreEnrichedDiagram.{u} (r + 1)).obj
    ((oneDirectionIndex r).obj (fun _ => n))
  have h := types_congr_hom (NatTrans.congr_app (quasicategoryEnrichedAction_unit G C) n) z
  exact (stableOneDirectionAction_app r C C n z.1 ((eId SSet.{u} C).app n z.2)).trans h

/-- 概要：元の全作用は高次入力の合成を保存する。
方針：同じ次数の core 関手の三作用を回収して合成則を使う。
規約：全パラメータの等式。使われ方：同じ商作用の合成則。 -/
lemma stableOneDirectionAction_comp (r : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionAction r C D ⊗ₘ 𝟙 (D ⟶[SSet.{u}] E)) ≫
        stableOneDirectionAction r D E =
      (α_ ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C))
        (C ⟶[SSet.{u}] D) (D ⟶[SSet.{u}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{u} C D E) ≫ stableOneDirectionAction r C E := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  let G := (stableMultiSCoreEnrichedDiagram.{u} (r + 1)).obj
    ((oneDirectionIndex r).obj (fun _ => n))
  have ha := stableOneDirectionAction_app r C D n z.1.1 z.1.2
  have hb := stableOneDirectionAction_app r D E n
    ((stableOneDirectionAction r C D).app n z.1) z.2
  have hc := stableOneDirectionAction_app r C E n z.1.1
    ((eComp SSet.{u} C D E).app n (z.1.2, z.2))
  have h := types_congr_hom (NatTrans.congr_app (quasicategoryEnrichedAction_comp G C D E) n) z
  exact hb.trans ((congrArg (fun x => (uncurry (G.map D E)).app n (x, z.2)) ha).trans
    (h.trans hc.symm))

end SerrePositivity.KST.SConstruction
