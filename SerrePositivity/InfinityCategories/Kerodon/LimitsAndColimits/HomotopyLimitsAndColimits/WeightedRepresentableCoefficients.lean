module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.RepresentableComparison

/-!
概要：表現可能な反転係数の評価の合成則を豊穣 Hom の合成として表す。
方針：豊穣 Hom 関手の射の作用を定値 simplex との豊穣合成として計算する。
規約：通常の図式 F の射を豊穣 Hom の零単体からの定値射へ写す。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4（Tag 03B5） の coherent cone の豊穣関手の組立て。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplicialThickening CartesianMonoidalCategory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：豊穣 Hom 関手の共変作用は通常の射の定値 simplex との豊穣合成。
方針：whiskering の定義を展開し、単位からの射の定値性を使う。
規約：単体の次数は任意。Kan 性は不要。
使われ方：HTT 4.2.4.1 の係数図式の作用と cone の合成則の同定。 -/
lemma simplicialHomWhiskerLeft_app {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x : C) {y z : C} (f : y ⟶ z) (d : SimplexCategoryᵒᵖ)
    (a : (SimplicialCategory.sHom x y).obj d) :
    (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map f).app d a =
      (eComp SSet x y z).app d
        (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' y z f) d.unop.len) := by
  change (eComp SSet x y z).app d (a, (eHomEquiv SSet f).app d PUnit.unit) = _
  rcases d with ⟨⟨d⟩⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant]
  rfl

/-- 概要：表現可能な係数の評価は非定値 Hom と図式の定値 Hom の豊穣合成を保つ。
方針：係数の path 合成則を各 simplex で評価し、共変 Hom の作用を豊穣合成へ置き換える。
規約：正の切断点 i.succ と終点 j.succ の順序を明示する。
使われ方：HTT 4.2.4.1 の weighted nerve から coherent cone への非定値合成則。 -/
lemma weightedRepresentableCoefficient_comp {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) (x : C)
    {n : ℕ} {σ : ComposableArrows I n}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (i j : Fin (n + 1)) (h : i ≤ j) (d : SimplexCategoryᵒᵖ)
    (P : (nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up i.succ))).obj d)
    (Q : (nerve (Path (ULift.up i.succ : ULift.{u} (Fin (n + 2)))
      (ULift.up j.succ))).obj d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ j).app d
      ((eComp SSet
        (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩).app d (P, Q)) =
    (eComp SSet x (F.obj (σ.obj i)) (F.obj (σ.obj j))).app d
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient τ i).app d P,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
          (F.map (σ.map (homOfLE h)))) d.unop.len) := by
  have hc := congrArg
    (fun t : (SimplicialCategory.sHom
        (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⊗ SimplicialCategory.sHom
        (⟨ULift.up i.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.succ⟩) ⟶ SimplicialCategory.sHom x (F.obj (σ.obj j)) ↦
      t.app d (P, Q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedCoherentCoefficient_comp τ i j h)
  exact hc.trans (simplicialHomWhiskerLeft_app x (F.map (σ.map (homOfLE h))) d _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
