module

public import SerrePositivity.KST.Spectra.SquareTriangleRestriction
public import SerrePositivity.KST.Spectra.TrianglePairDesc

/-!
概要：正方形の三角形への制限と相対三角形の貼り合わせの往復。
方針：正方形と相対三角形の二つの pushout の普遍性で判定する。
規約：往復はホモトピーでなく厳密な等式。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。貼り合わせによる写像の普遍性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：四辺で定数な正方形の写像を制限して貼ると元へ戻る。
方針：正方形の二つの三角形上で復元の式を使う。
規約：対角辺での一致には制限の標準の等式を使う。
使われ方：Goerss–Jardine I §7。三角形分割による写像の普遍性の一方の往復。 -/
theorem trianglePairSquare_restrictions (Y : PointedSimplicialSet.{u})
    (f : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right) (hl hr) :
    trianglePairSquare (squareUpperRestriction Y f hl hr) (squareLowerRestriction Y f hl hr)
      (squareRestrictions_diagonal Y f hl hr) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext <;> simp

/-- 概要：貼った正方形を上側の相対三角形へ制限すると第一の写像に戻る。
方針：相対三角形の cofiber の商射上で検査する。
規約：四辺の定数性は貼り合わせから得た標準の証明を使う。
使われ方：Kerodon §3.2.3（Tag 00W3）。三角形分割の普遍性のもう一方の往復。 -/
theorem squareUpperRestriction_pair {Y : PointedSimplicialSet.{u}}
    (a b : triangleDisk.{u} ⟶ Y) (h : triangleDiskDiagonal ≫ a = triangleDiskDiagonal ≫ b) :
    squareUpperRestriction Y (trianglePairSquare a b h)
      (trianglePairSquare_boundary_left a b h) (trianglePairSquare_boundary_right a b h) = a := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp

/-- 概要：貼った正方形を下側の相対三角形へ制限すると第二の写像に戻る。
方針：cofiber の商射上の制限の式を使う。
規約：上側と同じ境界条件の証明を使う。
使われ方：Kerodon §3.2.3（Tag 00W3）。相対三角形の貼り合わせの一意性。 -/
theorem squareLowerRestriction_pair {Y : PointedSimplicialSet.{u}}
    (a b : triangleDisk.{u} ⟶ Y) (h : triangleDiskDiagonal ≫ a = triangleDiskDiagonal ≫ b) :
    squareLowerRestriction Y (trianglePairSquare a b h)
      (trianglePairSquare_boundary_left a b h) (trianglePairSquare_boundary_right a b h) = b := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp

end

end SerrePositivity.KST.Spectra
