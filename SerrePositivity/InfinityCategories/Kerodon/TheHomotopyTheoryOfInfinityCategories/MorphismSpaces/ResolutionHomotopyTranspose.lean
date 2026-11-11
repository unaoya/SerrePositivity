module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHornProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionMonomorphisms

/-!
# 解像の随伴による単体的ホモトピーの転置

概要：解像からの射のホモトピーは右随伴を標的とする射のホモトピーへ移せる。
方針：解像の射影の自然性で円筒の比較射を作り、随伴の自然性で両端を計算する。
規約：円筒の比較射を同型と仮定しない。
使われ方：HA 1.3.1.17、Kerodon Theorem 4.6.7.5（Tag 01LE） の解像の射影から右随伴の比較への接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial

/-- 概要：積の解像から解像と単位区間の積への標準の比較射。
方針：第一成分は解像で第一射影を写し、第二成分は自然な射影の後に第二射影を取る。
規約：積との厳密な可換性や同型は仮定しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の随伴でホモトピーを転置する円筒の比較。 -/
def resolutionCylinderMap (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj (A ⊗ Δ[1]) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj A ⊗ Δ[1] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (fst A Δ[1]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (A ⊗ Δ[1]) ≫ snd A Δ[1])

/-- 概要：円筒の比較射は零端点を保つ。
方針：二つの射影の後で関手性と解像の射影の自然性を使う。
規約：零端点の厳密な射の等式。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の転置したホモトピーの始端。 -/
lemma resolutionCylinderMap_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ≫ resolutionCylinderMap A = SSet.ι₀ := by
  dsimp only [resolutionCylinderMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, ← Functor.map_comp, SSet.ι₀_fst]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map_id A
  · rw [Category.assoc, lift_snd, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality, Category.assoc, SSet.ι₀_snd]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app A ≫ SSet.ι₀ ≫ snd A Δ[1] = _
    rw [SSet.ι₀_snd A]
    exact SSet.comp_const _ _

/-- 概要：円筒の比較射は一端点を保つ。
方針：二つの射影の後で関手性と自然性を使う。
規約：一端点の厳密な射の等式。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の転置したホモトピーの終端。 -/
lemma resolutionCylinderMap_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ≫ resolutionCylinderMap A = SSet.ι₁ := by
  dsimp only [resolutionCylinderMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, ← Functor.map_comp, SSet.ι₁_fst]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map_id A
  · rw [Category.assoc, lift_snd, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality, Category.assoc, SSet.ι₁_snd]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app A ≫ SSet.ι₁ ≫ snd A Δ[1] = _
    rw [SSet.ι₁_snd A]
    exact SSet.comp_const _ _

/-- 概要：解像からの二射のホモトピーを随伴によって転置する。
方針：円筒の比較射を前合成してから随伴対応を取り、両端の式で端点を確認する。
規約：始域・終域の Kan 性は不要。
使われ方：HA 1.3.1.17 の比較射の実際のホモトピー逆の構成。 -/
def resolutionHomotopyTranspose {A K : SSet.{u}}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj A ⟶ K} (H : SSet.Homotopy f g) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv A K f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv A K g) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv (A ⊗ Δ[1]) K (resolutionCylinderMap A ≫ H.h)
  h₀ := by
    change SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv (A ⊗ Δ[1]) K)
      (resolutionCylinderMap A ≫ H.h) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv A K f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv A K)
    rw [← Category.assoc, resolutionCylinderMap_zero, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv (A ⊗ Δ[1]) K)
      (resolutionCylinderMap A ≫ H.h) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv A K g
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left]
    apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv A K)
    rw [← Category.assoc, resolutionCylinderMap_one, H.h₁]
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

/-- 概要：射影の後の射の随伴転置はその射の後の標準比較射である。
方針：随伴の右自然性と標準比較射の自然性を合わせる。
規約：任意の二つの単体集合とその間の射に適用できる。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の逆構成の合成の計算。 -/
lemma resolutionHomEquiv_projection_comp {A K : SSet.{u}} (g : A ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv A K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app A ≫ g) =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison K := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_right]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparisonNat.naturality g).symm

/-- 概要：随伴の余単位の転置は右随伴上の恒等射である。
方針：随伴対応の余単位の計算則を使う。
規約：任意の単体集合 K。
使われ方：HA 1.3.1.17 の右随伴の比較射の合成のホモトピーの終端。 -/
lemma resolutionHomEquiv_counit (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj K) K
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.counit.app K) = 𝟙 _ := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj K) K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.counit.app K) = 𝟙 _
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj K) K).symm (𝟙 _) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.counit.app K := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_counit, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map_id, Category.id_comp]
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj K) K) h
  simpa only [Equiv.apply_symm_apply] using he.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
