module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonEpi

/-!
概要：左右の写像空間から区間模型への比較射の単射性。
方針：一点因子を補う直積の射が同型であることと fat join 比較のエピ性を使う。
規約：標的の quasicategory 性は単射性には不要。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、写像空間の比較に沿う相対的な延長。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右の点で等しい join 図式は右円筒への引き戻しで区別できる。
方針：点を補う直積の射の同型性で円柱を回収し、fat join のエピな比較を消去する。
規約：A が空の場合も右の点での等式を明示する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、右 pinched 模型の比較の単射性。 -/
lemma rightMappingSpacePrism_hom_ext {A X : SSet.{u}} {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ g)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ g) : f = g := by
  let l : Δ[1] ⊗ A ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u}) :=
    (β_ Δ[1] A).hom ≫
      lift (𝟙 (A ⊗ Δ[1])) (SSet.const (stdSimplex.obj₀Equiv.symm 0))
  have hi : IsIso (lift (𝟙 (A ⊗ Δ[1]))
      (SSet.const (stdSimplex.obj₀Equiv.symm 0)) :
      A ⊗ Δ[1] ⟶ (A ⊗ Δ[1]) ⊗ (Δ[0] : SSet.{u})) :=
    IsIso.of_isIso_fac_right (lift_fst _ _)
  have : Epi l := by dsimp [l]; infer_instance
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap A Δ[0] ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap A Δ[0] ≫ g := by
    apply (cancel_epi l).1
    exact h
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A Δ[0])).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison] using hc
  · have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ z) h
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_zero,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison] using hh
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison] using hy

/-- 概要：左の点で等しい join 図式は左円筒への引き戻しで区別できる。
方針：点を補った円柱の第二射影が同型であることと fat join の外延性を使う。
規約：A が空の場合も左の点での等式を明示する。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、coslice fiber の比較の単射性。 -/
lemma leftMappingSpacePrism_hom_ext {A X : SSet.{u}} {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) A ⟶ X}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism A ≫ g)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] A ≫ g) : f = g := by
  let l : Δ[1] ⊗ A ⟶ ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ A :=
    lift (lift (SSet.const (stdSimplex.obj₀Equiv.symm 0)) (fst Δ[1] A)) (snd Δ[1] A)
  have he : l ≫ (snd (Δ[0] : SSet.{u}) Δ[1] ▷ A) = 𝟙 _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have : IsIso l := IsIso.of_isIso_fac_right he
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[0] A ≫ g := by
    apply (cancel_epi l).1
    exact h
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] A)).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison] using hc
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison] using hx
  · have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ z) h
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_one,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison] using hh

/-- 概要：右 pinched 模型から区間模型への比較射は単射。
方針：任意の族を join 図式に展開し、右円筒の外延性で比較する。
規約：X の Kan 性も quasicategory 性も不要。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、右模型を区間模型への包含として扱う。 -/
instance pinchedHomToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) := by
  constructor
  intro A f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_injective x y
  apply rightMappingSpacePrism_hom_ext
  · have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry] using hh
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inr]

/-- 概要：coslice fiber から区間模型への比較射は単射。
方針：fiber への族を join 図式に展開し、左円筒の外延性を使う。
規約：左の点での等式は coslice の固定条件から従う。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、unstraightening の fiber の相対比較。 -/
instance cosliceFiberToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y) := by
  constructor
  intro A f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_injective x y
  apply leftMappingSpacePrism_hom_ext
  · have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_uncurry] using hh
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inl]

/-- 概要：左 pinched 模型から区間模型への比較射も単射。
方針：coslice fiber との同型とその区間比較の単射性を合成する。
規約：左模型は Core の反転による定義を用いる。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の模型の対称な相対比較。 -/
instance pinchedHomLeftToIntervalMappingSpace_mono {X : SSet.{u}} (x y : X _⦋0⦌) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace x y) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
