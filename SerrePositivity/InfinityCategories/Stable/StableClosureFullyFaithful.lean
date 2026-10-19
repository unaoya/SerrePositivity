module
public import SerrePositivity.InfinityCategories.Stable.StableHoGeneration
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Core.FullyFaithful

/-! # 完全充満忠実関手による実安定閉包の保存と反映

概要：安定 ∞ 圏間の完全充満忠実関手は、指定頂点の実安定閉包への所属を保存・反映する。
方針：h の三角的対象条件の本質像と逆像の生成性を使い、同型を充満忠実性で戻す。
規約：対象の本質的全射性は要求しない。使われ方：Yoneda 模型から元の dg 圏へ分母を戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]

/-- 実安定閉包への所属は完全充満忠実関手で保存・反映される。 -/
theorem stableVertexClosure_image_iff (F : X ⟶ Y) [IsExactFunctor F]
    (hf : IsFullyFaithful F) (P : Set (X _⦋0⦌)) (x : X _⦋0⦌) :
    StableVertexClosure (F.app (Opposite.op ⦋0⦌) '' P) (F.app (Opposite.op ⦋0⦌) x) ↔
      StableVertexClosure P x := by
  let H := (hoFunctor.map F).toFunctor
  let : H.Full := hf.toHoFullyFaithful.full
  let : H.Faithful := hf.toHoFullyFaithful.faithful
  let R := stableHoClosure P
  let S := stableHoClosure (F.app (Opposite.op ⦋0⦌) '' P)
  constructor
  · intro hx
    have hle : S ≤ R.map H := by
      refine (stableHoClosure_le_iff (X := Y) _ (R.map H)).mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact R.prop_map_obj H (X := SSet.HomotopyCategory.mk a) (StableVertexClosure.of_mem ha)
    obtain ⟨a, ha, ⟨e⟩⟩ := hle
      (SSet.HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x)) hx
    exact R.prop_of_iso
      (H.preimageIso (X := a) (Y := SSet.HomotopyCategory.mk x) e) ha
  · intro hx
    have hle : R ≤ S.inverseImage H := by
      refine (stableHoClosure_le_iff (X := X) P (S.inverseImage H)).mpr ?_
      intro a ha
      exact StableVertexClosure.of_mem ⟨a, ha, rfl⟩
    exact hle (SSet.HomotopyCategory.mk x) hx

end SerrePositivity.InfinityCategories
