module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedNativeCone

/-!
概要：指定 BK 錐入力に全豊穣 Hom パラメータを前合成する比較射。
方針：反転した豊穣合成を全添字に使い、重み付き end の普遍性でまとめる。
規約：元の錐入力と全単体パラメータを保持する。同値性は別に示す。
使われ方：HA 1.2.4、G10 の元の Tot の全 Hom 試験。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (F : I ⥤ C) (z : C)
variable (φ : bousfieldKanWeight I ⟶ simplicialHomDiagram F z ⋙ SSet.opFunctor)

/-- 指定錐の全成分に、反転豊穣 Hom の同じ全パラメータを前合成する。 -/
def reflectedWeightedHomFamily (x : C) :
    bousfieldKanWeight I ⊗ (Functor.const I).obj (SimplicialCategory.sHom x z).op ⟶
      simplicialHomDiagram F x ⋙ SSet.opFunctor where
  app i := (φ.app i ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom ≫ SSet.opFunctor.map (eComp SSet x z (F.obj i))
  naturality i j f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    rintro ⟨w, g⟩
    have hp := ConcreteCategory.congr_hom (NatTrans.congr_app (φ.naturality f) n) w
    have hc := congrArg (fun (h :
        (SimplicialCategory.sHom x z ⊗ SimplicialCategory.sHom z (F.obj i)) ⟶
          SimplicialCategory.sHom x (F.obj j)) => h.app n (g, (φ.app i).app n w))
      (eComp_eHomWhiskerLeft SSet x z (F.map f))
    change (eComp SSet x z (F.obj j)).app n
        (g, (φ.app j).app n ((bousfieldKanWeight I).map f |>.app n <| w)) =
      (eHomWhiskerLeft SSet x (F.map f)).app n
        ((eComp SSet x z (F.obj i)).app n (g, (φ.app i).app n w))
    change (φ.app j).app n ((bousfieldKanWeight I).map f |>.app n <| w) =
      (eHomWhiskerLeft SSet z (F.map f)).app n ((φ.app i).app n w) at hp
    rw [hp]
    exact hc.symm

/-- 元の指定錐からの全豊穣 Hom 比較。 -/
def reflectedWeightedHomComparison (x : C) :
    (SimplicialCategory.sHom x z).op ⟶
      bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor) :=
  weightedSectionsLift (reflectedWeightedHomFamily F z φ x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
