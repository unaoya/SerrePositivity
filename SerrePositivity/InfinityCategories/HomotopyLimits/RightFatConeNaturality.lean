module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFatConeDiagram

/-!
概要：右パラメータ付き fat join 図式の一意性とパラメータへの自然性。
方針：左端と右直積比較への引き戻しで射を決定し、普遍族の前合成の式を使う。
規約：空のパラメータも扱い、右直積比較自体のエピ性は要求しない。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断側の標準比較と部分族の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：右パラメータ付き fat join 上の射は左端と右直積比較への引き戻しで決まる。
方針：円柱では並べ替えの同型を消去し、右端では右直積比較の制限を使う。
規約：パラメータ P の非空性を要求しない。
使われ方：Kerodon §4.6.6 の固定左端を保つ図式の一意性。 -/
lemma fatJoinTensorRight_hom_ext {A B P X : SSet.{u}}
    {F G : fatJoin A (B ⊗ P) ⟶ X}
    (hl : fatJoinInl A (B ⊗ P) ≫ F = fatJoinInl A (B ⊗ P) ≫ G)
    (hc : fatJoinTensorRight A B P ≫ F = fatJoinTensorRight A B P ≫ G) : F = G := by
  apply fatJoin_hom_ext
  · have h := congrArg (fun z ↦ (fatJoinCylinder A B ▷ P) ≫ z) hc
    simp only [← Category.assoc, fatJoinTensorRight_cylinder] at h
    change (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom ≫ fatJoinCylinder A (B ⊗ P) ≫ F =
      (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom ≫ fatJoinCylinder A (B ⊗ P) ≫ G at h
    exact (cancel_epi (α_ (A ⊗ (Δ[1] : SSet.{u})) B P).hom).mp h
  · exact hl
  · have h := congrArg (fun z ↦ (fatJoinInr A B ▷ P) ≫ z) hc
    simpa only [← Category.assoc, fatJoinTensorRight_inr] using h

/-- 概要：固定頂点の普遍族の展開はパラメータの前合成を保つ。
方針：内部 Hom の uncurry の前合成の自然性を使う。
規約：固定頂点と右図式は共通。
使われ方：Kerodon §4.6.6 の右パラメータの図式への自然性。 -/
lemma fixedFatConeFamily_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ fixedEndpointFatConeSpace p x) (a : A ⟶ B) :
    fixedFatConeFamily (a ≫ f) = (fatJoin (Δ[0] : SSet.{u}) K ◁ a) ≫ fixedFatConeFamily f := by
  unfold fixedFatConeFamily
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：右パラメータの fat join 図式はパラメータの前合成と可換。
方針：左端と右直積比較への引き戻しの一意性を使い、普遍族の自然性へ帰着する。
規約：パラメータの射に単射性は不要。
使われ方：Kerodon §4.6.6 の部分族上で一致する相対 join 延長の準備。 -/
lemma rightFatConeDiagram_precomp {A B K X : SSet.{u}} {p : K ⟶ X} {x : X _⦋0⦌}
    (f : B ⟶ fixedEndpointFatConeSpace p x) (a : A ⟶ B) :
    rightFatConeDiagram (a ≫ f) =
      fatJoinMap (𝟙 (Δ[0] : SSet.{u})) (K ◁ a) ≫ rightFatConeDiagram f := by
  apply fatJoinTensorRight_hom_ext
  · rw [rightFatConeDiagram_inl, ← Category.assoc, fatJoinInl_map, Category.id_comp,
      rightFatConeDiagram_inl]
  · rw [rightFatConeDiagram_family, ← Category.assoc, ← fatJoinTensorRight_parameter,
      Category.assoc, rightFatConeDiagram_family, fixedFatConeFamily_precomp]

/-- 概要：固定頂点の錐の族は右パラメータの fat join 図式から一意に回収できる。
方針：右直積比較で元の普遍族へ戻し、uncurry と fiber の包含の単射性を使う。
規約：充填性の仮定は不要。
使われ方：Kerodon §4.6.6、7.4.1.6 の標準比較の単射性の検査。 -/
lemma rightFatConeDiagram_injective {A K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :
    Function.Injective (rightFatConeDiagram (A := A) (p := p) (x := x)) := by
  intro f g h
  have hc := congrArg (fun z ↦ fatJoinTensorRight (Δ[0] : SSet.{u}) K A ≫ z) h
  rw [rightFatConeDiagram_family, rightFatConeDiagram_family] at hc
  apply vertexFiber_hom_ext ((pre (fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
  exact uncurry_injective hc

end SerrePositivity.InfinityCategories.HomotopyLimits
