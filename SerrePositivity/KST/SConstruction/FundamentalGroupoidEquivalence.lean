module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FundamentalGroupoidComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-! # 元の辺と二単体の基本亜群と Kan 置換のホモトピー圏の同値
概要：Kan 値 anodyne 射の基本亜群比較は実際の圏同値である。
方針：元の源上の厳密な逆律と anodyne ホモトピー延長で二つの逆律を得る。
規約：全頂点間の射を比較し、基点だけに弱めない。使われ方：K 空間の生成・関係の表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- もう一方の逆律の二つの nerve 値写像は、元の単体集合上で厳密に一致する。 -/
lemma fundamentalGroupoidComparison_right_restriction {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) :
    i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse i hi ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i) =
        i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (𝟭 (hoFunctor.obj B)) := by
  simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose_pre, ← CategoryTheory.Functor.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison_fac,
    CategoryTheory.Functor.comp_id]

/-- 基本亜群比較の逆向き合成は、Kan 対象のホモトピー圏上で恒等関手と自然同型。 -/
def fundamentalGroupoidComparison_rightInverse {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse i hi ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i ≅
      𝟭 (hoFunctor.obj B) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse i hi ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveTranspose (𝟭 (hoFunctor.obj B))
  have he : i ≫ f = i ≫ g := fundamentalGroupoidComparison_right_restriction i hi
  have H₀ : SSet.Homotopy (i ≫ f) (i ≫ g) := by
    rw [he]
    exact SSet.RelativeMorphism.Homotopy.refl _
  have hK : modelCategoryQuillen.J.rlp (terminal.from (nerve (hoFunctor.obj B))) :=
    (modelCategoryQuillen.fibration_iff _).mp inferInstance
  let H := Classical.choice (KanHomotopyExtension.exists_homotopy i hi hK f g H₀)
  exact (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_transpose
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse i hi ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.fundamentalNerveUntransposeHomotopy H ≪≫
        eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose_transpose (𝟭 (hoFunctor.obj B)))

/-- Kan 値 anodyne 射は元の辺と二単体の基本亜群を Kan ホモトピー圏と同値にする。 -/
def fundamentalGroupoidEquivalence {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A ≌ hoFunctor.obj B :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidInverse i hi)
    (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison_leftInverse i hi)).symm
    (fundamentalGroupoidComparison_rightInverse i hi)

/-- 比較は元の任意の二頂点間の全ての形式的な道を忠実充満に写す。 -/
def fundamentalGroupoidComparison_fullyFaithful {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).FullyFaithful :=
  (fundamentalGroupoidEquivalence i hi).fullyFaithfulFunctor

/-- Kan 値 anodyne 射の後の任意の射は、元の辺の形式的逆と合成で表示される。 -/
lemma fundamentalGroupoidComparison_map_surjective {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).map :
      (x ⟶ y) → ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj x ⟶
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj y)) :=
  (fundamentalGroupoidComparison_fullyFaithful i hi).map_surjective

/-- 元の道の二つの表示が Kan 対象で一致すれば、元の基本亜群で既に一致する。 -/
lemma fundamentalGroupoidComparison_map_injective {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplicialFundamentalGroupoid A) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).map :
      (x ⟶ y) → ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj x ⟶
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).obj y)) :=
  (fundamentalGroupoidComparison_fullyFaithful i hi).homEquiv.injective

end SerrePositivity.KST.SConstruction
