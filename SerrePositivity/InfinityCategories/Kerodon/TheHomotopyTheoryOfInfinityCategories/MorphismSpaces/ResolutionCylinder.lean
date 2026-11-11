module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionRightKan

/-!
概要：解像の円筒の比較と随伴によるホモトピーの転置。
方針：第一射影を解像で写し、第二射影は一般の射影を通して単位区間へ写す。
規約：解像が直積を保存するとは主張しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 4.6.7.16（Tag 01LQ）、比較射のホモトピー逆。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：円筒を解像したものから解像の円筒への比較射。
方針：第一成分に第一射影の像、第二成分に一般の射影の後の第二射影を使う。
規約：円筒の単位区間は Δ[1]。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、随伴でホモトピーを移すための比較。 -/
noncomputable def coherentResolutionCylinderComparison (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj (K ⊗ Δ[1]) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj K ⊗ Δ[1] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (fst K Δ[1]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (K ⊗ Δ[1]) ≫ snd K Δ[1])

/-- 概要：円筒の比較は零端点を保つ。
方針：二つの成分で比較し、第一成分は射影、第二成分は定値射として計算する。
規約：解像の円筒の始端は標準の ι₀。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、転置したホモトピーの始端。 -/
lemma coherentResolutionCylinderComparison_zero (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) ≫ coherentResolutionCylinderComparison K =
      SSet.ι₀ := by
  unfold coherentResolutionCylinderComparison
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, ← CategoryTheory.Functor.map_comp,
      SSet.ι₀_fst, CategoryTheory.Functor.map_id, SSet.ι₀_fst]
  · have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (K ⊗ Δ[1]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ SSet.ι₀ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality SSet.ι₀
    rw [Category.assoc, lift_snd, ← Category.assoc, hn]
    rfl

/-- 概要：円筒の比較は一端点を保つ。
方針：射影と定値射の計算を一端点で行う。
規約：解像の円筒の終端は標準の ι₁。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、転置したホモトピーの終端。 -/
lemma coherentResolutionCylinderComparison_one (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) ≫ coherentResolutionCylinderComparison K =
      SSet.ι₁ := by
  unfold coherentResolutionCylinderComparison
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, ← CategoryTheory.Functor.map_comp,
      SSet.ι₁_fst, CategoryTheory.Functor.map_id, SSet.ι₁_fst]
  · have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (K ⊗ Δ[1]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ SSet.ι₁ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality SSet.ι₁
    rw [Category.assoc, lift_snd, ← Category.assoc, hn]
    rfl

/-- 概要：解像からの二つの射のホモトピーを右随伴への二つの射のホモトピーにする。
方針：円筒の比較を前合成し、随伴対応で射と端点の式を移す。
規約：標的の Kan 性や quasicategory 性はこの構成には不要。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の普遍性のホモトピーとの整合性。 -/
noncomputable def coherentResolutionTransposeHomotopy {K Z : SSet.{u}}
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj K ⟶ Z} (H : SSet.Homotopy a b) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z b) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv (K ⊗ Δ[1]) Z
    (coherentResolutionCylinderComparison K ≫ H.h)
  h₀ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left, ← Category.assoc,
      coherentResolutionCylinderComparison_zero, H.h₀]
    rfl
  h₁ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left, ← Category.assoc,
      coherentResolutionCylinderComparison_one, H.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：一般の射影の後の射を随伴で移すと比較射による後合成。
方針：一般の射影の自然性と随伴の左変数の自然性を使う。
規約：任意の単体集合 K,Z と射 b に適用する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、比較射による写像の回収。 -/
lemma coherentResolutionHomEquiv_projection_comp {K Z : SSet.{u}} (b : K ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ b) =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z := by
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality b
  rw [← hn, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left]
  rfl

/-- 概要：Kan 複体への右随伴の射は比較射の後合成としてホモトピーまで回収できる。
方針：一般の射影の前合成の本質的全射性で射を選び、その同型のホモトピーを転置する。
規約：関手単体集合のホモトピー圏の同型として述べる。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射のホモトピー逆の一方。 -/
lemma coherentResolutionComparison_postcomp_essentiallySurjective {K Z : SSet.{u}} [KanComplex Z]
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) :
    ∃ b : K ⟶ Z, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison Z) a) := by
  let a' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z).symm a
  obtain ⟨v, ⟨e⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence K Z).choose.isEssentiallySurjective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a')
  obtain ⟨b, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K Z).surjective v
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ b) a' := e
  let H := coherentResolutionTransposeHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy e')
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app K ≫ b))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv K Z a') at he
  rw [coherentResolutionHomEquiv_projection_comp] at he
  exact ⟨b, ⟨by simpa only [a', Equiv.apply_symm_apply] using he⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
