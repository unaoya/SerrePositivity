module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeHomProduct

/-! # Hom に移したループ積の後合成自然性

概要：対称 span の余極限頂点からの Hom 上の演算は任意の射による後合成に自然。
方針：射を辺で代表し、共通始点から選んだ整合する輸送と積の基点独立性を使う。
規約：終点ごとの枝の基点は自由に選べる。使われ方：加法の一般判定の自然性条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：対称 span の余極限頂点からの Hom 上の演算は、任意の頂点間の射による後合成に自然。
方針：共通始点の輸送を枝と全体へ持ち上げ、Hom 表示の後合成公式と積の保存を使う。
規約：零射や前加法構造は不要。両端の枝の基点は任意。使われ方：演算の加法との照合。 -/
lemma symmetricCoconeHomProduct_naturality {X : SSet.{u}} [Quasicategory X]
    {x z : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (hz : IsZeroVertex z) (c : JoinCocone (edgeSpan f f)) (hc : IsColimitCone c)
    (y₀ y₁ : X _⦋0⦌)
    (e₀ : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₀) _⦋0⦌)
    (e₁ : (coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y₁) _⦋0⦌)
    (u v : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y₀)
    (h : (SSet.HomotopyCategory.mk y₀ : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y₁) :
    symmetricCoconeHomProduct f hz c hc y₀ e₀ u v ≫ h =
      symmetricCoconeHomProduct f hz c hc y₁ e₁ (u ≫ h) (v ≫ h) := by
  obtain ⟨a, rfl⟩ := homotopyCategory_homMk_surjective y₀ y₁ h
  obtain ⟨S⟩ := nonempty_coconeEndpointTransport
    (stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge) a
  obtain ⟨T, U, _, hT, h₁, h₂⟩ := exists_symmetricCoconeEndpointTransport f a S
  obtain ⟨b, rfl⟩ := (coconeMappingSpacePiZeroEquiv c hc y₀).surjective u
  obtain ⟨d, rfl⟩ := (coconeMappingSpacePiZeroEquiv c hc y₀).surjective v
  rw [symmetricCoconeHomProduct_apply,
    ← coconeMappingSpacePiZeroEquiv_transport c hc a U,
    symmetricCoconeLoopProduct_transport_basepoints f hz.1 a S T U hT h₁ h₂ e₀ e₁,
    ← symmetricCoconeHomProduct_apply,
    coconeMappingSpacePiZeroEquiv_transport c hc a U,
    coconeMappingSpacePiZeroEquiv_transport c hc a U]

end SerrePositivity.InfinityCategories
