module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceRoofNativeRoofComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantSourceFrameGraph

/-!
概要：元の comma augmentation roof は同じ弱な balanced frame 比較の全族である。
方針：元の全単体の三頂点・二射と全縦射を厳密に照合する。
規約：包含の逆の選択や別の代表族を使わない。
使われ方：指定次数の native roof と同じ弱基準射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped _root_.Simplicial
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)
  (b : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：元の augmentation roof の全 graph は元の frame graph の同じ制限。
方針：元の三頂点・二射・全縦射を全単体で回収する。
規約：元の全射の等式。使われ方：余極限での同じ全基準族。 -/
lemma modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap_image :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap X Y q b =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameGraphMap X Y q := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let F := ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap X Y q b).app n) σ
  let G := ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameGraphMap X Y q).app n) σ
  have ho (i : Fin (n.unop.len + 1)) : F.obj i = G.obj i := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro j
      change Fin 3 at j
      fin_cases j <;> rfl
    · intro j
      change Fin 2 at j
      fin_cases j <;> rfl
  apply Functor.hext ho
  intro i j f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change Fin 3 at k
  fin_cases k <;> rfl

/-- 概要：元の augmentation roof の余極限像は同じ弱な全 frame 比較。
方針：元の graph 等式を同じ全語標準射へ合成する。
規約：元の全比較射自身。使われ方：native 評価 roof の弱基準族への接続。 -/
lemma modelBifibrantSourceRoofProductCommaAugmentationRoofMap_image :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofMap X Y q b =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaFirstNerve X Y q b ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameColimitMap X Y q := by
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap X Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceRoofProductCommaAugmentationRoofGraphMap_image,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantSourceFrameGraphMap_colimit]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
