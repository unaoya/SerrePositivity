module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：重みの同じパラメーター付きホモトピーを、元の切断制限のホモトピーへ移す。
方針：元の普遍評価を、重みと区間の同じパラメーターで前合成して転置する。
規約：IS-W2 R03a.1の重みの前合成の法則。成分ごとの別々の逆射ではない。
使われ方：境界右持ち上げ性を持つ重みの射の切断と収縮の輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の重みの区間パラメーターを同じ普遍評価へ代入した自然変換。 -/
def weightedSourceHomotopySection {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (weightedSections W H ⊗ (Δ[1] : SSet.{u})) ⟶ H where
  app i :=
    { app d := ↾fun x =>
        ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app d
          ((T.app i).app d (x.1, x.2.2), x.2.1)
      naturality d e α := by
        apply ConcreteCategory.hom_ext
        rintro ⟨v, s, t⟩
        change ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app e
          ((T.app i).app e ((V.obj i).map α v, (Δ[1] : SSet.{u}).map α t),
            (weightedSections W H).map α s) = _
        let z : ((V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})).obj i).obj d := (v, t)
        have ht := NatTrans.naturality_apply (T.app i) α z
        change (T.app i).app e ((V.obj i).map α v, (Δ[1] : SSet.{u}).map α t) =
          (W.obj i).map α ((T.app i).app d (v, t)) at ht
        rw [ht]
        let z' : ((W ⊗ (Functor.const I).obj (weightedSections W H)).obj i).obj d :=
          ((T.app i).app d (v, t), s)
        exact NatTrans.naturality_apply
          ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i) α z' }
  naturality i j f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨v, s, t⟩
    let z : ((V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})).obj i).obj d := (v, t)
    have ht := ConcreteCategory.congr_hom (NatTrans.congr_app (T.naturality f) d) z
    change (T.app j).app d ((V.map f).app d v, t) =
      (W.map f).app d ((T.app i).app d (v, t)) at ht
    change ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app j).app d
      ((T.app j).app d ((V.map f).app d v, t), s) = _
    rw [ht]
    let z' : ((W ⊗ (Functor.const I).obj (weightedSections W H)).obj i).obj d :=
      ((T.app i).app d (v, t), s)
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app ((weightedSectionsUncurry (𝟙 (weightedSections W H))).naturality f) d) z'

/-- 元の重みの同じ区間ホモトピーを転置した、切断空間上の写像。 -/
def weightedSourceHomotopyMap {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    weightedSections W H ⊗ (Δ[1] : SSet.{u}) ⟶ weightedSections V H :=
  weightedSectionsLift (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopySection I T H)

/-- 元の図式の区間の第零端点を全自然変換として読む。 -/
def weightIntervalZero (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) where
  app _ := SSet.ι₀
  naturality i j f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl

/-- 元の図式の区間の第一端点を全自然変換として読む。 -/
def weightIntervalOne (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) where
  app _ := SSet.ι₁
  naturality i j f := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    rfl

/-- 同じ区間の転置は、元の第零端点での制限射を保つ。 -/
theorem weightedSourceHomotopyMap_zero {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalZero I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₀ ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap I T H = weightedSectionsPre f H := by
  apply (weightedSectionsHomEquiv V H (weightedSections W H)).injective
  change weightedSectionsUncurry (SSet.ι₀ ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap I T H) =
    weightedSectionsUncurry (weightedSectionsPre f H)
  rw [weightedSectionsUncurry_precomp, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap,
    weightedSectionsUncurry_lift, weightedSectionsPre, weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨v, s⟩
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h i) d) v
  exact congrArg (fun w => ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app d
    (w, s)) he

/-- 同じ区間の転置は、元の第一端点での制限射を保つ。 -/
theorem weightedSourceHomotopyMap_one {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalOne I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₁ ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap I T H = weightedSectionsPre f H := by
  apply (weightedSectionsHomEquiv V H (weightedSections W H)).injective
  change weightedSectionsUncurry (SSet.ι₁ ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap I T H) =
    weightedSectionsUncurry (weightedSectionsPre f H)
  rw [weightedSectionsUncurry_precomp, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap,
    weightedSectionsUncurry_lift, weightedSectionsPre, weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨v, s⟩
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h i) d) v
  exact congrArg (fun w => ((weightedSectionsUncurry (𝟙 (weightedSections W H))).app i).app d
    (w, s)) he


/-- 同じ重みのホモトピーの両端点を保ち、元の切断空間の実際のホモトピーへ運ぶ。 -/
def weightedSectionsPreHomotopy {V W : I ⥤ SSet.{u}} {f g : V ⟶ W}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h₀ : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalZero I V ≫ T = f) (h₁ : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightIntervalOne I V ≫ T = g)
    (H : I ⥤ SSet.{u}) : SSet.Homotopy (weightedSectionsPre f H) (weightedSectionsPre g H) where
  h := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap I T H
  h₀ := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap_zero I T f h₀ H
  h₁ := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSourceHomotopyMap_one I T g h₁ H
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, t⟩
    exact hx.elim

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
