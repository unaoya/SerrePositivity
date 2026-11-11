module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightFatConeDiagram

/-!
概要：右パラメータ付き fat join 図式の一意性とパラメータへの自然性。
方針：左端と右直積比較への引き戻しで射を決定し、普遍族の前合成の式を使う。
規約：空のパラメータも扱い、右直積比較自体のエピ性は要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の切断側の標準比較と部分族の整合性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右パラメータ付き fat join 上の射は左端と右直積比較への引き戻しで決まる。
方針：円柱では並べ替えの同型を消去し、右端では右直積比較の制限を使う。
規約：パラメータ P の非空性を要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY） の固定左端を保つ図式の一意性。 -/
lemma fatJoinTensorRight_hom_ext {A B P X : SSet.{u}}
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A (B ⊗ P) ⟶ X}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P) ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A (B ⊗ P) ≫ G)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight A B P ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight A B P ≫ G) : F = G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · have h := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ P) ≫ z) hc
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_cylinder] at h
    change (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P) ≫ F =
      (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A (B ⊗ P) ≫ G at h
    exact (cancel_epi (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom).mp h
  · exact hl
  · have h := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ P) ≫ z) hc
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_inr] using h

/-- 概要：固定頂点の普遍族の展開はパラメータの前合成を保つ。
方針：内部 Hom の uncurry の前合成の自然性を使う。
規約：固定頂点と右図式は共通。
使われ方：Kerodon §4.6.6（Tag 04HY） の右パラメータの図式への自然性。 -/
lemma fixedFatConeFamily_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeFamily (a ≫ f) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeFamily f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeFamily
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：右パラメータの fat join 図式はパラメータの前合成と可換。
方針：左端と右直積比較への引き戻しの一意性を使い、普遍族の自然性へ帰着する。
規約：パラメータの射に単射性は不要。
使われ方：Kerodon §4.6.6（Tag 04HY） の部分族上で一致する相対 join 延長の準備。 -/
lemma rightFatConeDiagram_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace p x) (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram (a ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 (Δ[0] : SSet.{u})) (K ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram f := by
  apply fatJoinTensorRight_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_inl]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight_parameter,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family, fixedFatConeFamily_precomp]

/-- 概要：固定頂点の錐の族は右パラメータの fat join 図式から一意に回収できる。
方針：右直積比較で元の普遍族へ戻し、uncurry と fiber の包含の単射性を使う。
規約：充填性の仮定は不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の標準比較の単射性の検査。 -/
lemma rightFatConeDiagram_injective {A K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram (A := A) (p := p) (x := x)) := by
  intro f g h
  have hc := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorRight (Δ[0] : SSet.{u}) K A ≫ z) h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightFatConeDiagram_family] at hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
  exact uncurry_injective hc

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
