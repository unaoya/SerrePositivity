module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoGeneration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-! # 完全充満忠実関手による実安定閉包の保存と反映

概要：安定 ∞ 圏間の完全充満忠実関手は、指定頂点の実安定閉包への所属を保存・反映する。
方針：h の三角的対象条件の本質像と逆像の生成性を使い、同型を充満忠実性で戻す。
規約：対象の本質的全射性は要求しない。使われ方：Yoneda 模型から元の dg 圏へ分母を戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]

/-- 実安定閉包への所属は完全充満忠実関手で保存・反映される。 -/
theorem stableVertexClosure_image_iff (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful F) (P : Set (X _⦋0⦌)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (F.app (Opposite.op ⦋0⦌) '' P) (F.app (Opposite.op ⦋0⦌) x) ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x := by
  let H := (hoFunctor.map F).toFunctor
  let : H.Full := hf.toHoFullyFaithful.full
  let : H.Faithful := hf.toHoFullyFaithful.faithful
  let R := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P
  let S := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (F.app (Opposite.op ⦋0⦌) '' P)
  constructor
  · intro hx
    have hle : S ≤ R.map H := by
      refine (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff (X := Y) _ (R.map H)).mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact R.prop_map_obj H (X := SSet.HomotopyCategory.mk a) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ha)
    obtain ⟨a, ha, ⟨e⟩⟩ := hle
      (SSet.HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x)) hx
    exact R.prop_of_iso
      (H.preimageIso (X := a) (Y := SSet.HomotopyCategory.mk x) e) ha
  · intro hx
    have hle : R ≤ S.inverseImage H := by
      refine (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff (X := X) P (S.inverseImage H)).mpr ?_
      intro a ha
      exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨a, ha, rfl⟩
    exact hle (SSet.HomotopyCategory.mk x) hx

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
