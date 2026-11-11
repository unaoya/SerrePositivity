module
public import SerrePositivity.KST.SConstruction.IdentityPushoutUnion
public import SerrePositivity.KST.SConstruction.StablePushoutFamilies

/-! # 恒等な枝を持つ span の同時正規化
概要：どちらかの枝が恒等である全 span の族を標準四角形へ送る、全 span 上の切断を作る。
方針：二つの像の和に指定した標準族を、単射に沿って厳密に延長する。
規約：恒等の両向きの条件を同じ切断で満たす。使われ方：Fiore–Pieper Proposition 3.28 の K-L1 版。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：二つの恒等 span 族を同時に固定する全 span 上の切断が存在する。
方針：二つの像の和の包含に対して相対切断の延長を適用する。
規約：別々の切断の選択ではない。使われ方：正規化した単一の pushout の選択。 -/
lemma exists_jointNormalizedPushoutSection (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    ∃ s : (ihom (horn 2 0 : SSet.{u})).obj C ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagrams C,
      (identitySpanSubcomplex C).ι ≫ s = identityUnionPushoutFamily C ∧
        s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C = 𝟙 _ :=
  exists_stablePushoutSection_extending (identitySpanSubcomplex C).ι
    (identityUnionPushoutFamily C) (identityUnionPushoutFamily_projection C)

/-- 概要：恒等な枝を持つ span の両向きで同時に正規化した押し出しの選択。
方針：二つの像の和を保持する相対切断から選ぶ。
規約：全パラメーターの族に対する単体的射。使われ方：McCarthy 法の functorial pushout。
-/
def jointNormalizedPushoutSection (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (ihom (horn 2 0 : SSet.{u})).obj C ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutDiagrams C :=
  Classical.choose (exists_jointNormalizedPushoutSection C)

/-- 概要：同時正規化した選択は入力 span を厳密に回収する。
方針：選択の仕様の切断の条件。
規約：ホモトピー等号に弱めない。使われ方：任意の入力での二辺の回収。 -/
lemma jointNormalizedPushoutSection_projection (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    jointNormalizedPushoutSection C ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutProjection C = 𝟙 _ :=
  (Classical.choose_spec (exists_jointNormalizedPushoutSection C)).2

/-- 概要：同時正規化した選択は二つの像の和で標準族を回収する。
方針：選択の仕様の相対条件。
規約：部分複体の全単体での等号。使われ方：各向きの正規化の回収。 -/
lemma jointNormalizedPushoutSection_union (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (identitySpanSubcomplex C).ι ≫ jointNormalizedPushoutSection C =
      identityUnionPushoutFamily C :=
  (Classical.choose_spec (exists_jointNormalizedPushoutSection C)).1

private def identitySpanIntoUnion (b : Bool) (C : SSet.{u}) :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ (identitySpanSubcomplex C : SSet.{u}) :=
  Subcomplex.lift (identitySpanFamily b C) (by
    cases b
    · exact le_sup_left
    · exact le_sup_right)

private lemma identitySpanIntoUnion_square (b : Bool) (C : SSet.{u}) :
    identitySpanIntoUnion b C ≫ identityUnionSquare C =
      (pre (identityPushoutShape b)).app C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  exact identityUnionSquare_on_family C b n g ((identitySpanIntoUnion b C).app n g) rfl

/-- 概要：同じ切断が両向きの恒等 span で標準四角形を厳密に回収する。
方針：各像を二つの像の和へ持ち上げ、和での正規化を制限する。
規約：頂点だけでなく任意の高次の族での等号。使われ方：McCarthy の退化・端点の照合。 -/
lemma jointNormalizedPushoutSection_identity (b : Bool) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    identitySpanFamily b C ≫ jointNormalizedPushoutSection C = identityPushoutFamily b C := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsPushoutDiagramVertex).ι).1
  rw [Category.assoc, identityPushoutFamily_ι]
  have hi : identitySpanIntoUnion b C ≫ (identitySpanSubcomplex C).ι = identitySpanFamily b C := rfl
  rw [← hi, Category.assoc, ← Category.assoc (identitySpanSubcomplex C).ι,
    jointNormalizedPushoutSection_union]
  exact identitySpanIntoUnion_square b C

/-- 概要：同時に正規化した選択と以前の選択は入力 span 上の関手として同型。
方針：同じ入力に持ち上がる二つの族を比較する。
規約：既存の切断の公開型を変更しない。使われ方：以前の構成との比較。 -/
def jointNormalizedPushoutSection_comparison (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (jointNormalizedPushoutSection C) (stablePushoutSection C) :=
  stablePushoutFamiliesIso (𝟙 _) _ _ (jointNormalizedPushoutSection_projection C)
    (stablePushoutSection_projection C)

end SerrePositivity.KST.SConstruction
