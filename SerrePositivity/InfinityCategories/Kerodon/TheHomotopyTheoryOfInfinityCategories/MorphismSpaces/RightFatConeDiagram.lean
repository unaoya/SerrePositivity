module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorRightComparison

/-!
概要：両端固定の fat join の錐の族を、右因子にパラメータを持つ fat join 図式へ展開する。
方針：関手空間の普遍族を円柱で評価し、固定頂点と元の右図式に貼る。
規約：パラメータ A を K との直積の右因子とする。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の相対 join 延長の入力。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定頂点の fat join の錐の族を関手空間から直積上へ展開する。
方針：両端固定の fiber の包含を uncurry する。
規約：錐の形が第一因子、パラメータが第二因子。
使われ方：Kerodon §4.6.6（Tag 04HY） の右パラメータの fat join 図式の構成。 -/
noncomputable def fixedFatConeFamily {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ⊗ A ⟶ X :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion Δ[0] K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p)))

/-- 概要：直積上の普遍族の左端は指定頂点の一点の族。
方針：両端固定の左制限を uncurry する。
規約：パラメータを忘れた一点への射を通る。
使われ方：Kerodon §4.6.6（Tag 04HY） の円柱の零端の整合性。 -/
lemma fixedFatConeFamily_inl {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A) ≫ fixedFatConeFamily f =
      fst (Δ[0] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm x := by
  rw [fixedFatConeFamily, ← uncurry_pre_app, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeSpace_inl,
    SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：直積上の普遍族の右端は元の図式の定値族。
方針：両端固定の右制限を uncurry する。
規約：第一射影でパラメータを忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の円柱の一端の整合性。 -/
lemma fixedFatConeFamily_inr {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ≫ fixedFatConeFamily f = fst K A ≫ p := by
  rw [fixedFatConeFamily, ← uncurry_pre_app, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeSpace_inr,
    SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：固定頂点の錐の族を右因子にパラメータを持つ fat join 上の図式にする。
方針：円柱の直積の結合順序を変え、固定した左右の図式と貼り合わせる。
規約：右端では K の成分だけを保持する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の部分族を保つ join 延長。 -/
noncomputable def rightFatConeDiagram {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (SSet.yonedaEquiv.symm x) (fst K A ≫ p)
    ((α_ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) K A).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K ▷ A) ≫ fixedFatConeFamily f)
    (by
      have h : (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ (K ⊗ A)) ≫
          (α_ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) K A).inv =
          (α_ (Δ[0] : SSet.{u}) K A).inv ≫ ((SSet.ι₀ ▷ K) ▷ A) := rfl
      rw [← Category.assoc (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ (K ⊗ A)), h]
      simp only [Category.assoc]
      rw [← Category.assoc ((SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ K) ▷ A),
        ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero, comp_whiskerRight]
      simp only [Category.assoc]
      rw [fixedFatConeFamily_inl]
      rfl)
    (by
      have h : (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ (K ⊗ A)) ≫
          (α_ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) K A).inv =
          (α_ (Δ[0] : SSet.{u}) K A).inv ≫ ((SSet.ι₁ ▷ K) ▷ A) := rfl
      rw [← Category.assoc (SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ (K ⊗ A)), h]
      simp only [Category.assoc]
      rw [← Category.assoc ((SSet.ι₁ (X := (Δ[0] : SSet.{u})) ▷ K) ▷ A),
        ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one, comp_whiskerRight]
      simp only [Category.assoc]
      rw [fixedFatConeFamily_inr]
      rfl)

/-- 概要：右パラメータの fat join 図式の左端は指定頂点。
方針：貼り合わせの左包含上の計算。
規約：一点から X への Yoneda 射を使う。
使われ方：Kerodon §4.6.6（Tag 04HY） の相対 join 延長の固定頂点。 -/
lemma rightFatConeDiagram_inl {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) (K ⊗ A) ≫ rightFatConeDiagram f = SSet.yonedaEquiv.symm x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：右パラメータの fat join 図式の右端は元の図式の定値族。
方針：貼り合わせの右包含上の計算。
規約：第一射影で A を忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の相対 join 延長の固定図式。 -/
lemma rightFatConeDiagram_inr {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) (K ⊗ A) ≫ rightFatConeDiagram f = fst K A ≫ p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：右パラメータの図式を fat join の右直積比較で引き戻すと元の普遍族。
方針：円柱と左右の包含で比較し、円柱では直積の結合同型を打ち消す。
規約：充填性なしの射の厳密な等式。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の二つのパラメータ表示の整合性。 -/
lemma rightFatConeDiagram_family {A K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight (Δ[0] : SSet.{u}) K A ≫ rightFatConeDiagram f = fixedFatConeFamily f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_tensorRight_hom_ext
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder (Δ[0] : SSet.{u}) K ▷ A),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_cylinder, Category.assoc, rightFatConeDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc]
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRightCylinderShuffle (Δ[0] : SSet.{u}) K A =
        (α_ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) K A).hom := rfl
    rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[0] : SSet.{u}) K ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_inl,
      Category.assoc, rightFatConeDiagram_inl, fixedFatConeFamily_inl]
  · rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_inr,
      rightFatConeDiagram_inr, fixedFatConeFamily_inr]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
