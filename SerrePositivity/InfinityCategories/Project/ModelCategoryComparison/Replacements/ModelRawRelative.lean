module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelCofibrantHammockWeak

/-!
概要：宇宙を持ち上げる前の元のモデル圏と両全部分圏の相対比較を公開する。
方針：同じ実単位・余単位を元の全 hammock Hom 射へ適用する。
規約：対象と Hom の元の宇宙を保ち、全圏側には第一の関手的分解を明示する。
使われ方：元の source frame roof の包含像と ambient 比較の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory _root_.HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：元の cofibrant 全部分圏上の弱同値。
方針：元の包含に沿う逆像。規約：宇宙を上げない。
使われ方：元の frame Hom の実 nerve 比較。 -/
abbrev modelRawCofibrantWeak : MorphismProperty (CofibrantObject C) :=
  (weakEquivalences C).inverseImage CofibrantObject.ι

/-- 概要：元の bifibrant 全部分圏上の弱同値。
方針：同じ元の包含に沿う逆像。規約：宇宙を上げない。
使われ方：元の frame の両性質の同時保持。 -/
abbrev modelRawBifibrantWeak : MorphismProperty (BifibrantObject C) :=
  (weakEquivalences C).inverseImage BifibrantObject.ι

/-- 概要：元の bifibrant 包含の相対関手。
方針：同じ射の弱同値性を読む。規約：元の包含自身。
使われ方：元の hammock Hom の包含射。 -/
def modelRawBifibrantToCofibrant : LocalizerMorphism
    (modelRawBifibrantWeak (C := C)) (modelRawCofibrantWeak (C := C)) :=
  ⟨BifibrantObject.ιCofibrantObject, fun _ _ _ h => h⟩

/-- 概要：同じ right frame の次数零による元の bifibrant 化の相対関手。
方針：元の全弱同値の保存を読む。規約：同じ実置換。
使われ方：包含射の相対逆。 -/
def modelRawCofibrantToBifibrant
    (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) : LocalizerMorphism
      (modelRawCofibrantWeak (C := C)) (modelRawBifibrantWeak (C := C)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantToBifibrant r, fun _ _ f hf =>
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_map_weak r f.hom hf⟩

variable (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
include r in
/-- 概要：元の bifibrant 包含の全 hammock Hom 射自身は弱同値。
方針：同じ二つの弱単位を宇宙調整前の相対逆判定へ渡す。
規約：元の全 Hom。使われ方：ambient frame 比較の回収。 -/
lemma modelRawBifibrantToCofibrant_colimitMap_weak (X Y : BifibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap
      (modelRawBifibrantToCofibrant (C := C)) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.colimitMap_weak_of_units
    modelRawBifibrantToCofibrant (modelRawCofibrantToBifibrant r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.bifibrantCofibrantUnit r)
    (fun Z => (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Z.obj).2)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantBifibrantUnit r)
    (fun Z => (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Z.obj).2) X Y

/-- 概要：元の cofibrant 包含を全圏への相対関手にする。
方針：同じ射の弱同値性を読む。規約：元の包含自身。
使われ方：同じ ambient hammock Hom への写像。 -/
def modelRawCofibrantToModel : LocalizerMorphism
    (modelRawCofibrantWeak (C := C)) (weakEquivalences C) :=
  ⟨CofibrantObject.ι, fun _ _ _ h => h⟩

variable [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

/-- 概要：元の関手的 cofibrant 置換を同じ宇宙の相対関手にする。
方針：同じ全弱同値保存を使う。規約：第一の分解のみ。
使われ方：元の包含の逆候補。 -/
def modelRawToCofibrant : LocalizerMorphism (weakEquivalences C)
    (modelRawCofibrantWeak (C := C)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantReplacement C, fun _ _ f hf => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantReplacement_map_weak C f hf⟩

/-- 概要：元の cofibrant 包含の全 hammock Hom 射は弱同値。
方針：同じ元の置換の二つの弱余単位を使う。
規約：第一の関手的分解を明示。使われ方：ambient 比較の反映。 -/
lemma modelRawCofibrantToModel_colimitMap_weak (X Y : CofibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap
      (modelRawCofibrantToModel (C := C)) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.colimitMap_weak modelRawCofibrantToModel modelRawToCofibrant
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelCounit C)
    (fun Z => (ModelReplacement.cofibrantComparison_trivialFibration C Z.obj).2)
    (ModelReplacement.cofibrantComparison C)
    (fun Z => (ModelReplacement.cofibrantComparison_trivialFibration C Z).2) X Y

/-- 概要：元の bifibrant 全部分圏を同じ ambient 圏へ送る相対関手。
方針：元の二つの包含を合成する。規約：宇宙調整なし。
使われ方：元の frame roof の ambient 像。 -/
def modelRawBifibrantToModel : LocalizerMorphism
    (modelRawBifibrantWeak (C := C)) (weakEquivalences C) :=
  modelRawBifibrantToCofibrant.comp modelRawCofibrantToModel

include r in
/-- 概要：元の bifibrant 包含の全 ambient hammock Hom 射は弱同値。
方針：同じ二つの実包含の弱比較を合成する。
規約：元の全比較射自身。使われ方：実 frame 比較の弱同値性の反映。 -/
lemma modelRawBifibrantToModel_colimitMap_weak (X Y : BifibrantObject C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap
      (modelRawBifibrantToModel (C := C)) X Y) := by
  rw [modelRawBifibrantToModel, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap_comp]
  exact (modelRawBifibrantToCofibrant_colimitMap_weak r X Y).comp
    (modelRawCofibrantToModel_colimitMap_weak _ _)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
