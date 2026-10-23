module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorParameterizedPrismNaturality
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily

/-!
概要：coherent な変換の写像空間を底の射に沿って制限する。
方針：関手空間の前合成を区間模型へ適用し、普遍的な族の評価と照合する。
規約：底は任意で、変換の可逆性も仮定しない。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の写像空間の底変換の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の射への前合成は coherent な変換の空間の射を与える。
方針：内部 Hom の前合成に区間写像空間の後合成を適用する。
規約：写された端点は制限した二つの図式の関手頂点。
使われ方：Kerodon Remark 5.6.2.5、変換の空間における底変換。 -/
def leftUnstraighteningTransformationRestriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraighteningTransformationSpace F G ⟶
      leftUnstraighteningTransformationSpace (k ≫ F) (k ≫ G) :=
  intervalMappingPost ((pre k).app SpaceInfinity) (functorVertex F) (functorVertex G)

/-- 概要：変換の空間の制限を展開すると、元の区間の族への前合成になる。
方針：区間写像空間の後合成の評価公式を使う。
規約：区間と変換の空間をともに保持する。
使われ方：Kerodon Remark 5.6.2.5、制限後の普遍的な変換の評価の準備。 -/
lemma leftUnstraighteningTransformationRestriction_uncurry {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    intervalMappingUncurry (leftUnstraighteningTransformationRestriction F G k) =
      intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)) ≫
        (pre k).app SpaceInfinity := by
  simpa only [Category.id_comp, leftUnstraighteningTransformationRestriction,
    leftUnstraighteningTransformationSpace] using intervalMappingPost_uncurry
    ((pre k).app SpaceInfinity) (functorVertex F) (functorVertex G) (𝟙 _)

/-- 概要：変換を制限してから普遍的な族を評価すると、元の族の底に沿う制限と一致する。
方針：区間模型の評価と prism の二つの自然性を組み合わせる。
規約：等式は変換の空間全体をパラメーターとして厳密に成り立つ。
使われ方：Kerodon Remark 5.6.2.5、写像空間の比較に使う普遍的な持ち上げの底の同定。 -/
lemma leftUnstraighteningTransformationFamily_restriction {B D : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    ((Δ[1] ⊗ D) ◁ leftUnstraighteningTransformationRestriction F G k) ≫
      leftUnstraighteningTransformationFamily (k ≫ F) (k ≫ G) =
    ((Δ[1] ◁ k) ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G := by
  rw [leftUnstraighteningTransformationFamily, ← functorParameterizedPrism_parameter,
    ← intervalMappingUncurry_precomp, Category.comp_id,
    leftUnstraighteningTransformationRestriction_uncurry,
    functorParameterizedPrism_pre]
  rfl

end SerrePositivity.InfinityCategories
