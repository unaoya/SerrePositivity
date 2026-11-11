module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction
public import SerrePositivity.KST.Spectra.WeightCylinderFunctor

/-!
概要：重みの自然な cylinder を weighted end の前合成の単体的ホモトピーへ移す。
方針：重み・end の元・区間の三変数を並べ替え、cylinder と普遍的評価を合成する。
規約：重みや係数の Kan 性を仮定せず、実際の区間ホモトピーを構成する。
使われ方：Goerss–Jardine VII §4。置換した終頂点の重みの比較を end に送る。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

open scoped MonoidalClosed Simplicial

namespace SerrePositivity.KST.Spectra.WeightedPreHomotopy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I : Type u} [SmallCategory I]

/-- 三つの変数 (w,e,t) を ((w,t),e) に並べ替える射。 -/
def rearrange (A E T : SSet.{u}) : A ⊗ (E ⊗ T) ⟶ (A ⊗ T) ⊗ E :=
  lift (lift (fst A (E ⊗ T)) (snd A (E ⊗ T) ≫ snd E T))
    (snd A (E ⊗ T) ≫ fst E T)

/-- 重みの cylinder を普遍的な end の評価へ前合成した三変数の族。 -/
def family {W V : I ⥤ SSet.{u}}
    (C : W ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V) (H : I ⥤ SSet.{u}) :
    W ⊗ (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H ⊗ (Δ[1] : SSet.{u})) ⟶ H where
  app i := rearrange (W.obj i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H) (Δ[1] : SSet.{u}) ≫
    (C.app i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H) ≫ MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)
  naturality i j f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change (W.obj i).obj n × ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H).obj n × (Δ[1] : SSet.{u}).obj n) at x
    have hC := C.naturality f
    change (W.map f ▷ (Δ[1] : SSet.{u})) ≫ C.app j = C.app i ≫ V.map f at hC
    have hc := congrArg (fun k : W.obj i ⊗ (Δ[1] : SSet.{u}) ⟶ V.obj j ↦
      k.app n (x.1, x.2.2)) hC
    change (C.app j).app n ((W.map f).app n x.1, x.2.2) =
      (V.map f).app n ((C.app i).app n (x.1, x.2.2)) at hc
    have he := congrArg (fun k : V.obj i ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H ⟶ H.obj j ↦
      k.app n ((C.app i).app n (x.1, x.2.2), x.2.1))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H))).naturality f)
    change (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H j)).app n
      ((C.app j).app n ((W.map f).app n x.1, x.2.2), x.2.1) =
      (H.map f).app n ((MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n
        ((C.app i).app n (x.1, x.2.2), x.2.1))
    rw [hc]
    exact he

/-- 零端で三変数の族を制限すると元の重みの射への前合成になる。 -/
lemma family_zero {W V : I ⥤ SSet.{u}}
    (C : W ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V)
    (θ : W ⟶ V) (hC : ∀ i, SSet.ι₀ ≫ C.app i = θ.app i) (H : I ⥤ SSet.{u}) (i : I) :
    (W.obj i ◁ (SSet.ι₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H ⟶ _)) ≫ (family C H).app i =
      (θ.app i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H) ≫ MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hC i) n) x.1
  change (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n
      ((C.app i).app n (SSet.ι₀.app n x.1), x.2) =
    (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n ((θ.app i).app n x.1, x.2)
  change (C.app i).app n (SSet.ι₀.app n x.1) = (θ.app i).app n x.1 at h
  exact congrArg (fun z ↦ (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n (z, x.2)) h

/-- 一端での同じ計算。 -/
lemma family_one {W V : I ⥤ SSet.{u}}
    (C : W ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V)
    (θ : W ⟶ V) (hC : ∀ i, SSet.ι₁ ≫ C.app i = θ.app i) (H : I ⥤ SSet.{u}) (i : I) :
    (W.obj i ◁ (SSet.ι₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H ⟶ _)) ≫ (family C H).app i =
      (θ.app i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections V H) ≫ MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hC i) n) x.1
  change (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n
      ((C.app i).app n (SSet.ι₁.app n x.1), x.2) =
    (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n ((θ.app i).app n x.1, x.2)
  change (C.app i).app n (SSet.ι₁.app n x.1) = (θ.app i).app n x.1 at h
  exact congrArg (fun z ↦ (MonoidalClosed.uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ V H i)).app n (z, x.2)) h

/-- 重みの自然な図式 cylinder は end の前合成の実際の単体的ホモトピーを与える。 -/
def homotopy {W V : I ⥤ SSet.{u}} {θ η : W ⟶ V}
    (C : W ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V)
    (h₀ : ∀ i, SSet.ι₀ ≫ C.app i = θ.app i)
    (h₁ : ∀ i, SSet.ι₁ ≫ C.app i = η.app i) (H : I ⥤ SSet.{u}) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre η H) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (family C H)
  h₀ := by
    change SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (family C H) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre θ H
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
    intro i
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π,
      ← curry_natural_left, family_zero C θ h₀ H i, ← curry_pre_app, curry_uncurry]
  h₁ := by
    change SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (family C H) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre η H
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
    intro i
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π,
      ← curry_natural_left, family_one C η h₁ H i, ← curry_pre_app, curry_uncurry]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x ↦ False.elim x.1.property)

end
end SerrePositivity.KST.Spectra.WeightedPreHomotopy
