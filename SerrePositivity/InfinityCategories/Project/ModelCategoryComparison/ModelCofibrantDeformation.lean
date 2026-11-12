module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelRelative
public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement

/-!
概要：指定関手的 cofibrant 分解による全モデル圏と cofibrant 相対圏の実変形。
方針：既存の一般 cofibrant 置換を全部分圏と同じ宇宙へ持ち上げる。
規約：この補助入口では関手的第一分解を明示入力に残す。
使われ方：実 dg モデルの同じ第一分解による全 C の指定局所化との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra
open _root_.SerrePositivity.ModelReplacement
variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

/-- 概要：既存の一般置換を元の cofibrant 全部分圏へ持ち上げる。
方針：元の全値の cofibrancy を読む。
規約：同じ関手的第一分解。使われ方：全 C からの実変形。 -/
def modelCofibrantReplacement : C ⥤ CofibrantObject C :=
  (cofibrantObjects C).lift (cofibrantReplacement C) (cofibrantReplacement_isCofibrant C)

/-- 概要：同じ一般 cofibrant 置換は元の弱同値を保つ。
方針：元の比較の自然性と二対三を使う。
規約：全 C の元の全射。使われ方：全相対圏への関手化。 -/
lemma modelCofibrantReplacement_map_weak {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) :
    weakEquivalences C ((cofibrantReplacement C).map f) := by
  apply (weakEquivalences C).of_postcomp _ ((cofibrantComparison C).app Y)
    (cofibrantComparison_trivialFibration C Y).2
  rw [(cofibrantComparison C).naturality f]
  exact (weakEquivalences C).comp_mem _ _ (cofibrantComparison_trivialFibration C X).2 hf

/-- 概要：全相対圏から同じ cofibrant 相対圏への実置換。
方針：既存の元の置換の前後で宇宙を揃える。
規約：同じ全対象と全射。使われ方：全 C の局所化比較の逆向き。 -/
def modelToCofibrant : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category ⥤
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).category :=
  AsSmall.down ⋙ modelCofibrantReplacement C ⋙ AsSmall.up

/-- 概要：元の実置換を同じ相対関手に束ねる。
方針：同じ元の弱同値保存を使う。
規約：同じ置換関手自身。使われ方：実 hammock Hom の比較。 -/
def modelToCofibrantRelative : LocalizerMorphism (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences :=
  ⟨modelToCofibrant C, fun _ _ f hf => modelCofibrantReplacement_map_weak C (AsSmall.down.map f) hf⟩

/-- 概要：cofibrant 部分圏上の同じ置換から恒等への比較。
方針：元の比較射を全部分圏の射にする。
規約：元の全自然変換を保持。使われ方：変形の部分圏側の逆合成。 -/
def cofibrantModelCounit : CofibrantObject.ι ⋙ modelCofibrantReplacement C ⟶
    𝟭 (CofibrantObject C) where
  app X := ObjectProperty.homMk ((cofibrantComparison C).app X.obj)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (cofibrantComparison C).naturality f.hom

/-- 概要：全相対圏の同じ置換の包含から恒等への比較。
方針：元の比較射と自然性の宇宙を揃える。
規約：同じ底の全比較。使われ方：変形の全 C 側の逆合成。 -/
def modelCofibrantCounit : modelToCofibrant C ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModel C ⟶
    𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category where
  app X := AsSmall.up.map ((cofibrantComparison C).app (AsSmall.down.obj X))
  naturality _ _ f := by
    apply ULift.ext
    exact (cofibrantComparison C).naturality (AsSmall.down.map f)

/-- 概要：cofibrant 相対圏上の同じ包含・置換から恒等への比較。
方針：部分圏の元の比較を同じ宇宙へ持ち上げる。
規約：同じ全自然変換。使われ方：実相対逆のもう一つの合成。 -/
def cofibrantModelSmallCounit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModel C ⋙ modelToCofibrant C ⟶
    𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).category where
  app X := AsSmall.up.map ((cofibrantModelCounit C).app (AsSmall.down.obj X))
  naturality _ _ f := by
    apply ULift.ext
    exact (cofibrantModelCounit C).naturality (AsSmall.down.map f)

/-- 概要：全 C 側の同じ比較の各成分は元の弱同値。
方針：元の cofibrant 比較の自明 fibration 性を使う。
規約：元の全相対圏の弱同値。使われ方：全反転関手上での可逆性。 -/
lemma modelCofibrantCounit_weak (X : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences ((modelCofibrantCounit C).app X) :=
  (cofibrantComparison_trivialFibration C (AsSmall.down.obj X)).2

/-- 概要：cofibrant 側の同じ比較の各成分も元の弱同値。
方針：同じ実比較の自明 fibration 性を読む。
規約：同じ底の射。使われ方：実相対逆の判定。 -/
lemma cofibrantModelSmallCounit_weak (X : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).category) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences
      ((cofibrantModelSmallCounit C).app X) :=
  (cofibrantComparison_trivialFibration C (AsSmall.down.obj X).obj).2

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
