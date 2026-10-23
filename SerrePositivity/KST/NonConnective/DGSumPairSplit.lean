module

public import SerrePositivity.KST.NonConnective.DGSumPairProjection

/-!
概要：同じ実二項 dg 関手直和の両注入・両射影の分裂公式。
方針：元の余積の普遍性の評価公式で四つの合成と恒等分解を計算する。
規約：直和を別の選択対象で置換しない。使われ方：同じ dg cone と Perf の分裂族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {C : Type w} [DGCategory R C]
  (F : WalkingPair → DGFunctor R C (ModuleCategory R D)) (X : C)

/-- 元の左注入と左射影は恒等射に合成する。 -/
lemma dgSumPair_left_left :
    Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.left ≫
      dgSumPairProjection R D F WalkingPair.left X = 𝟙 _ :=
  Sigma.ι_comp_desc _ WalkingPair.left

/-- 元の右注入と左射影の合成は零射。 -/
lemma dgSumPair_right_left :
    Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.right ≫
      dgSumPairProjection R D F WalkingPair.left X = 0 :=
  Sigma.ι_comp_desc _ WalkingPair.right

/-- 元の左注入と右射影の合成は零射。 -/
lemma dgSumPair_left_right :
    Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.left ≫
      dgSumPairProjection R D F WalkingPair.right X = 0 :=
  Sigma.ι_comp_desc _ WalkingPair.left

/-- 元の右注入と右射影は恒等射に合成する。 -/
lemma dgSumPair_right_right :
    Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.right ≫
      dgSumPairProjection R D F WalkingPair.right X = 𝟙 _ :=
  Sigma.ι_comp_desc _ WalkingPair.right

/-- 同じ二つの射影・注入の和は、元の実直和の恒等射。 -/
lemma dgSumPair_decomposition :
    dgSumPairProjection R D F WalkingPair.left X ≫
        Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.left +
      dgSumPairProjection R D F WalkingPair.right X ≫
        Sigma.ι (fun k ↦ (F k).obj X) WalkingPair.right =
      𝟙 (dgSumFamilyObj R D F X) := by
  apply Sigma.hom_ext
  intro k
  cases k <;>
    simp only [Preadditive.comp_add, ← Category.assoc, dgSumPair_left_left,
      dgSumPair_left_right, dgSumPair_right_left, dgSumPair_right_right,
      Category.id_comp, Category.comp_id, zero_comp, add_zero, zero_add]

end SerrePositivity.KST.NonConnective
