module

public import SerrePositivity.KST.Spectra.SquareBoundaryEdges

/-!
概要：四辺で定数な正方形の写像を二つの相対三角形へ制限する。
方針：外側の二辺が定数であるためホーンの商へ降ろす。
規約：二つの制限は共通の対角辺で厳密に一致する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。相対三角形の貼り合わせの逆構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : PointedSimplicialSet.{u})
  (f : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
  (hl : (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫ f =
    toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom)
  (hr : (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫ f =
    toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ Y.hom)

include hl hr

/-- 概要：上側の三角形のホーンでは正方形の写像は定数。
方針：ホーンを構成する二つの面で外側の辺の定数性を使う。
規約：ホーンは Λ[2,1]。
使われ方：Goerss–Jardine I §7。上側の相対三角形への降下条件。 -/
theorem square_upper_horn_constant :
    (horn.{u} 2 (1 : Fin 3)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f =
      toUnit (horn.{u} 2 (1 : Fin 3) : SSet.{u}) ≫ Y.hom := by
  apply horn.hom_ext'
  intro j hj
  simp only [horn.ι_ι_assoc, comp_toUnit_assoc]
  fin_cases j
  · exact square_upper_face_zero Y f hr
  · exact (hj rfl).elim
  · exact square_upper_face_last Y f hl

/-- 概要：下側の三角形のホーンでは正方形の写像は定数。
方針：ホーンの二つの面で縦辺と横辺の定数性を使う。
規約：上側と同じホーンを潰す。
使われ方：Goerss–Jardine I §7。下側の相対三角形への降下条件。 -/
theorem square_lower_horn_constant :
    (horn.{u} 2 (1 : Fin 3)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f =
      toUnit (horn.{u} 2 (1 : Fin 3) : SSet.{u}) ≫ Y.hom := by
  apply horn.hom_ext'
  intro j hj
  simp only [horn.ι_ι_assoc, comp_toUnit_assoc]
  fin_cases j
  · exact square_lower_face_zero Y f hl
  · exact (hj rfl).elim
  · exact square_lower_face_last Y f hr

/-- 概要：四辺で定数な正方形の写像の上側の相対三角形への制限。
方針：上側のホーンの定数性を cofiber の普遍性へ渡す。
規約：点つき射として構成する。
使われ方：Kerodon §3.2.3（Tag 00W3）。貼り合わせの逆写像。 -/
def squareUpperRestriction : triangleDisk.{u} ⟶ Y :=
  PointedObject.cofiberDesc (horn.{u} 2 (1 : Fin 3)).ι Y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f) (square_upper_horn_constant Y f hl hr)

/-- 概要：四辺で定数な正方形の写像の下側の相対三角形への制限。
方針：下側のホーンの定数性を cofiber の普遍性へ渡す。
規約：点つき射として構成する。
使われ方：Kerodon §3.2.3（Tag 00W3）。貼り合わせの逆写像。 -/
def squareLowerRestriction : triangleDisk.{u} ⟶ Y :=
  PointedObject.cofiberDesc (horn.{u} 2 (1 : Fin 3)).ι Y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f) (square_lower_horn_constant Y f hl hr)

/-- 概要：上側の制限を標準三角形へ戻すと元の写像の制限。
方針：cofiber の降下の標準射での式を使う。
規約：等式は基礎単体集合の射の等式。
使われ方：Goerss–Jardine I §7。制限と貼り合わせの往復。 -/
@[reassoc (attr := simp)]
theorem squareUpperRestriction_quotient :
    triangleDiskQuotient ≫ (squareUpperRestriction Y f hl hr).right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：下側の制限を標準三角形へ戻すと元の写像の制限。
方針：cofiber の降下の標準射での式を使う。
規約：上側と同じ商射を前合成する。
使われ方：Goerss–Jardine I §7。制限と貼り合わせの往復。 -/
@[reassoc (attr := simp)]
theorem squareLowerRestriction_quotient :
    triangleDiskQuotient ≫ (squareLowerRestriction Y f hl hr).right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：正方形からの二つの相対三角形の制限は対角辺で一致する。
方針：円の cofiber の普遍性で標準区間へ戻し、共通の対角辺を使う。
規約：同一の向きの対角辺の厳密な等式。
使われ方：Kerodon §3.2.3（Tag 00W3）。相対三角形の貼り合わせの両立条件。 -/
theorem squareRestrictions_diagonal :
    triangleDiskDiagonal ≫ squareUpperRestriction Y f hl hr =
      triangleDiskDiagonal ≫ squareLowerRestriction Y f hl hr := by
  apply PointedObject.cofiber_hom_ext (boundary.{u} 1).ι
  simp only [Under.comp_right, ← Category.assoc, triangleDiskDiagonal_quotient]
  rw [Category.assoc, Category.assoc, squareUpperRestriction_quotient,
    squareLowerRestriction_quotient, ← Category.assoc, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_diagonal, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_diagonal]

end

end SerrePositivity.KST.Spectra
