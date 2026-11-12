module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathIntervalCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeRestriction

/-!
# Path の区間制限写像の有限立方体による因子分解

概要：Path を別の区間へ制限する写像は、その区間にある有限座標への射影を通る。
方針：部分座標への制限と区間の有限集合への順序同型の像を比較する。
規約：座標の射影は部分型への逆像、座標の移送は順序同型の像を使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の合成面の左右の小さい立方体への移送。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
variable {J : Type u} [LinearOrder J] {a b c d : J}

/-- 概要：区間への Path の制限は区間内の有限座標の立方体を通る。
方針：単体の各頂点で選択した内部点の像を比較する。
規約：新しい両端点は制限後の pathCubeMap が付加する。
使われ方：Kerodon 2.5.9（Tag 00SC） の左右の Path を実際の有限立方体で表す。 -/
lemma pathCubeIntervalMap_factor (hcd : c < d) (S : Finset (Set.Ioo a b)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor hcd S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeRestrictionMap (fun t : S ↦ t.val.val ∈ Set.Ioo c d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeImageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S c d) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hcd (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S c d) := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  let U := F.obj t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hcd {z | ∃ v : S, v ∈ U ∧ v.val.val = z.val} =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInterior hcd ((Subtype.val : ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S c d) → Set.Ioo c d) ''
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S c d) ''
        {v : {v : S // v.val.val ∈ Set.Ioo c d} | v.val ∈ U}))
  congr 1
  rw [Set.image_image]
  apply Set.ext
  intro z
  change (∃ v : S, v ∈ U ∧ v.val.val = z.val) ↔
    ∃ w : {v : S // v.val.val ∈ Set.Ioo c d}, w.val ∈ U ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S c d w).val = z
  constructor
  · rintro ⟨v, hv, he⟩
    let w : {v : S // v.val.val ∈ Set.Ioo c d} := ⟨v, by rw [he]; exact z.property⟩
    exact ⟨w, hv, Subtype.ext he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨w.val, hw, congrArg Subtype.val he⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
