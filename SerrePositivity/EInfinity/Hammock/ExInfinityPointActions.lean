module

public import SerrePositivity.EInfinity.Hammock.ExInfinityEnrichedUnit
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PointActions

/-!
概要：同じ Ex∞ の lax monoidal 移送は元の指定点による後合成を保持する。
方針：同じ単位の自然性・tensor 自然性・右単位則を合成する。
規約：元の点・元の合成・同じ Ex∞ 単位を保持する。
使われ方：Kan hammock の豊穣後合成と元の strict Hom 図式の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.KST.Comparison

/-- 概要：元の点に Ex∞ 単位を合成した射は lax monoidal 単位からの像。
方針：同じ Ex∞ 単位の自然性と monoidal 単位則を使う。
規約：同じ実射。使われ方：移送した豊穣後合成。 -/
lemma exInfinityUnit_point {B : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ B) :
    p ≫ exInfinityUnit.app B = Functor.LaxMonoidal.ε exInfinity ≫ exInfinity.map p := by
  have h := exInfinityUnit.naturality p
  have hu : exInfinityUnit.app (𝟙_ SSet.{u}) = Functor.LaxMonoidal.ε exInfinity :=
    NatTrans.IsMonoidal.unit (τ := exInfinityUnit.{u})
  exact h.trans (congrArg (· ≫ exInfinity.map p) hu)

/-- 概要：同じ元の点による後合成と lax monoidal 移送は可換。
方針：同じ単位点の公式・tensor 自然性・右単位則を使う。
規約：元の合成 c を変更しない。
使われ方：元の strict 図式の Ex∞ 像と Kan 豊穣 Hom の全作用の一致。 -/
lemma exInfinity_postcompose_point {A B T : SSet.{u}}
    (p : 𝟙_ SSet.{u} ⟶ B) (c : A ⊗ B ⟶ T) :
    exInfinity.map ((ρ_ A).inv ≫ A ◁ p ≫ c) =
      (ρ_ (exInfinity.obj A)).inv ≫ exInfinity.obj A ◁ (p ≫ exInfinityUnit.app B) ≫
        Functor.LaxMonoidal.μ exInfinity A B ≫ exInfinity.map c := by
  rw [exInfinityUnit_point, whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]
  simp only [Functor.map_comp]

end SerrePositivity.EInfinity.Hammock
