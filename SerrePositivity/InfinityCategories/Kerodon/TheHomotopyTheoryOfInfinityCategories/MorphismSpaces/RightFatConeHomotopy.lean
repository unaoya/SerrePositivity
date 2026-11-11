module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightFatConeNaturality

/-!
概要：右パラメータ付きの fat join 図式の相対ホモトピーを、固定頂点の錐の族へ移す。
方針：右直積比較と結合同型でホモトピーを引き戻し、両端固定の fiber へ curry する。
規約：ホモトピーの全時間で頂点と元の図式を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断側の標準比較のホモトピー右逆。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右パラメータの fat join 図式のホモトピーを錐の形と時間付きパラメータへ展開する。
方針：結合同型で時間を分け、右直積比較を適用する。
規約：右の時間はホモトピーの区間。
使われ方：Kerodon §4.6.6（Tag 04HY） の関手空間へ curry するホモトピーの普遍族。 -/
noncomputable def rightFatConeHomotopyFamily {A K X : SSet.{u}}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X} (H : SSet.Homotopy F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ⊗ (A ⊗ Δ[1]) ⟶ X :=
  (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K) A Δ[1]).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight Δ[0] K A ▷ Δ[1]) ≫ H.h

/-- 概要：展開したホモトピーの左端は指定頂点の一点の族。
方針：右直積比較の左端の計算と元のホモトピーの固定左端を使う。
規約：全ての時間とパラメータで頂点を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の両端固定の fiber へ curry する左条件。 -/
lemma rightFatConeHomotopyFamily_inl {A K X : SSet.{u}} {x : X _⦋0⦌}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X} (H : SSet.Homotopy F G)
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ (A ⊗ Δ[1])) ≫ rightFatConeHomotopyFamily H =
      fst (Δ[0] : SSet.{u}) (A ⊗ Δ[1]) ≫ SSet.yonedaEquiv.symm x := by
  change (α_ (Δ[0] : SSet.{u}) A Δ[1]).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ▷ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight Δ[0] K A ▷ Δ[1]) ≫ H.h = _
  rw [← Category.assoc ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ▷ Δ[1]),
    ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_inl, comp_whiskerRight]
  simp only [Category.assoc]
  rw [hx]
  rfl

/-- 概要：展開したホモトピーの右端は元の図式の定値族。
方針：右直積比較の右端の計算と元のホモトピーの固定右端を使う。
規約：パラメータと時間を第一射影で忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の両端固定の fiber へ curry する右条件。 -/
lemma rightFatConeHomotopyFamily_inr {A K X : SSet.{u}} {p : K ⟶ X}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X} (H : SSet.Homotopy F G)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ fst K A ≫ p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ (A ⊗ Δ[1])) ≫ rightFatConeHomotopyFamily H =
      fst K (A ⊗ Δ[1]) ≫ p := by
  change (α_ K A Δ[1]).inv ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ▷ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight Δ[0] K A ▷ Δ[1]) ≫ H.h = _
  rw [← Category.assoc ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ▷ Δ[1]),
    ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_inr, hp]
  rfl

/-- 概要：右パラメータの図式の両端固定のホモトピーは固定頂点の錐の族のホモトピーを与える。
方針：展開したホモトピーを関手空間へ curry して fiber に持ち上げ、端点を計算する。
規約：充填性なしの実際のホモトピーの構成。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の比較のホモトピー右逆の回収。 -/
noncomputable def rightFatConeHomotopyOfDiagram {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x)
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram g))
    (hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ▷ Δ[1]) ≫ H.h =
      fst (K ⊗ A) Δ[1] ≫ fst K A ≫ p) : SSet.Homotopy f g := by
  have hc : curry (rightFatConeHomotopyFamily H) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointFunctor_hom_ext
    · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion,
        SSet.const_comp]
      change curry (rightFatConeHomotopyFamily H) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K)).app X =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm x))
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      exact rightFatConeHomotopyFamily_inl H hx
    · rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion,
        SSet.const_comp]
      change curry (rightFatConeHomotopyFamily H) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K)).app X =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      exact rightFatConeHomotopyFamily_inr H hp
  refine
    { h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry (rightFatConeHomotopyFamily H)) hc
      h₀ := ?_
      h₁ := ?_
      rel := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight (Δ[0] : SSet.{u}) K A ≫ SSet.ι₀ ≫ H.h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeFamily f
    rw [H.h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight (Δ[0] : SSet.{u}) K A ≫ SSet.ι₁ ≫ H.h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeFamily g
    rw [H.h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family]
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
