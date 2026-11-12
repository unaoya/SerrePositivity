module

public import SerrePositivity.KST.Spectra.TriangleDiskFaces
public import SerrePositivity.KST.Spectra.BoundaryTensorRightExt
public import SerrePositivity.KST.Spectra.SquareReducedDesc

/-!
概要：対角辺で一致する相対三角形の二つの写像を正方形に貼る。
方針：正方形の pushout と外側の四辺の消滅を使う。
規約：二つの相対三角形は同じ向きの対角辺を共有する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの円の交換の幾何的な模型。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : PointedSimplicialSet.{u}} (a b : triangleDisk.{u} ⟶ Y)
  (h : triangleDiskDiagonal ≫ a = triangleDiskDiagonal ≫ b)

/-- 概要：共通の対角辺で一致する相対三角形の写像を正方形へ貼る。
方針：三角形分割の pushout の普遍性を使う。
規約：上側が a、下側が b。
使われ方：Goerss–Jardine I §7。相対三角形の貼り合わせからの写像。 -/
def trianglePairSquare : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.desc (triangleDiskQuotient ≫ a.right)
    (triangleDiskQuotient ≫ b.right) (by
      rw [← triangleDiskDiagonal_quotient_assoc, ← triangleDiskDiagonal_quotient_assoc]
      exact congrArg (fun k : PointedSimplicialSet.circle.{u} ⟶ Y =>
        PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ k.right) h)

/-- 概要：貼った写像の上側への制限は元の第一の写像。
方針：pushout の第一の脚で計算する。
規約：相対三角形の商射を含む。
使われ方：Kerodon §3.2.3（Tag 00W3）。貼り合わせの復元。 -/
@[reassoc (attr := simp)]
theorem upper_trianglePairSquare :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ trianglePairSquare a b h = triangleDiskQuotient ≫ a.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inl_desc _ _ _

/-- 概要：貼った写像の下側への制限は元の第二の写像。
方針：pushout の第二の脚で計算する。
規約：上側と同じ相対三角形の商射を使う。
使われ方：Kerodon §3.2.3（Tag 00W3）。貼り合わせの復元。 -/
@[reassoc (attr := simp)]
theorem lower_trianglePairSquare :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ trianglePairSquare a b h = triangleDiskQuotient ≫ b.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.inr_desc _ _ _

/-- 概要：貼った正方形の縦の二辺は基点へ写る。
方針：境界との積を各端点で検査し、相対三角形の外側の辺を潰す。
規約：第一変数の境界を扱う。
使われ方：Goerss–Jardine I §7。第一の円への降下条件。 -/
theorem trianglePairSquare_boundary_left :
    (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫ trianglePairSquare a b h =
      toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom := by
  apply boundary_tensor_hom_ext
  intro j
  simp only [← comp_whiskerRight_assoc, boundary.ι_ι, comp_toUnit_assoc]
  fin_cases j
  · erw [SquareTriangles.first_endpoint_zero]
    simp only [Category.assoc, lower_trianglePairSquare,
      triangleDiskQuotient_outer_face_assoc (0 : Fin 3) (by decide),
      Under.w b, comp_toUnit_assoc]
  · erw [SquareTriangles.first_endpoint_one]
    simp only [Category.assoc, upper_trianglePairSquare,
      triangleDiskQuotient_outer_face_assoc (2 : Fin 3) (by decide),
      Under.w a, comp_toUnit_assoc]

/-- 概要：貼った正方形の横の二辺は基点へ写る。
方針：第二変数の各端点で相対三角形の外側の辺の消滅を使う。
規約：第二変数の境界を扱う。
使われ方：Goerss–Jardine I §7。第二の円への降下条件。 -/
theorem trianglePairSquare_boundary_right :
    (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫ trianglePairSquare a b h =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ Y.hom := by
  apply tensor_boundary_hom_ext
  intro j
  simp only [← whiskerLeft_comp_assoc, boundary.ι_ι, comp_toUnit_assoc]
  fin_cases j
  · erw [SquareTriangles.second_endpoint_zero]
    simp only [Category.assoc, upper_trianglePairSquare,
      triangleDiskQuotient_outer_face_assoc (0 : Fin 3) (by decide),
      Under.w a, comp_toUnit_assoc]
  · erw [SquareTriangles.second_endpoint_one]
    simp only [Category.assoc, lower_trianglePairSquare,
      triangleDiskQuotient_outer_face_assoc (2 : Fin 3) (by decide),
      Under.w b, comp_toUnit_assoc]

/-- 概要：対角辺で一致する二つの相対三角形の写像は円の smash 積へ貼れる。
方針：四辺の定数性を使って正方形の写像を降ろす。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の写像の普遍性。 -/
def trianglePairSmash : PointedObject.smash PointedSimplicialSet.circle.{u}
    PointedSimplicialSet.circle.{u} ⟶ Y :=
  SphereSimplex.squareSmashDesc Y (trianglePairSquare a b h)
    (trianglePairSquare_boundary_left a b h) (trianglePairSquare_boundary_right a b h)

/-- 概要：正方形の座標の交換は二つの相対三角形の写像を交換する。
方針：三角形分割の pushout の二つの脚で検査する。
規約：対角辺での一致の証明は対称にする。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの円の交換を貼り合わせの交換へ移す。 -/
theorem trianglePairSquare_swap :
    (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫ trianglePairSquare a b h =
      trianglePairSquare b a h.symm := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_swap]
    simp
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_swap]
    simp

/-- 概要：相対三角形から貼った smash の写像を正方形へ戻すと元の貼り合わせ。
方針：四辺を潰す降下の復元の式を使う。
規約：正方形から二つの円の smash 積への標準射を前合成する。
使われ方：Kerodon §3.2.3（Tag 00W3）。貼り合わせの普遍性の復元の計算。 -/
@[reassoc]
theorem trianglePairSmash_quotient :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right ≫ (trianglePairSmash a b h).right =
      trianglePairSquare a b h :=
  SphereSimplex.squareSmashDesc_quotient _ _ _ _

end

end SerrePositivity.KST.Spectra
