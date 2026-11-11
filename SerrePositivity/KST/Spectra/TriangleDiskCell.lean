module

public import SerrePositivity.KST.Spectra.TriangleDiskBoundary
public import SerrePositivity.KST.Spectra.BoundaryFaceCollapse
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：相対三角形を円へ二次元 cell を付けた対象として表示する。
方針：ホーンを潰した境界の付着写像を使って二つの pushout の普遍性を比較する。
規約：この表示から対角辺の包含の単射性を検査する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の写像空間の Kan fibration。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：三角形の二辺を基点へ、残る辺を円へ送る境界上の付着写像。
方針：ホーンを潰す標準の境界写像を二次元で使う。
規約：残る辺の添字は 1。
使われ方：Goerss–Jardine I §7。相対三角形の cell による表示。 -/
abbrev triangleAttachment : (boundary.{u} 2 : SSet.{u}) ⟶
    PointedSimplicialSet.circle.{u}.right := boundaryFaceCollapse.{u} 1 (1 : Fin 3)

/-- 概要：付着写像に沿い円へ二次元 cell を付けた点つき単体集合。
方針：境界包含と付着写像の通常の pushout を取る。
規約：基点は円の基点の像。
使われ方：Goerss–Jardine I §7、BF 1978 §2。対角辺の包含の単射性を検査する模型。 -/
def triangleCell : PointedSimplicialSet.{u} :=
  Under.mk (PointedSimplicialSet.circle.{u}.hom ≫ pushout.inr (boundary.{u} 2).ι triangleAttachment)

/-- 概要：二次元 cell から付着後の対象への標準射。
方針：pushout の標準射を使う。
規約：基点のない標準二単体を源とする。
使われ方：Goerss–Jardine I §7。ホーンの cofiber と比較する。 -/
abbrev triangleCellQuotient : (Δ[2] : SSet.{u}) ⟶ triangleCell.{u}.right :=
  pushout.inl (boundary.{u} 2).ι triangleAttachment

/-- 概要：円を cell 付着後の対象へ含める点つき射。
方針：pushout の円側の標準射を使う。
規約：円の基点は構成した対象の基点を定める。
使われ方：Goerss–Jardine I §7。相対三角形の対角辺の包含の比較。 -/
def triangleCellBoundary : PointedSimplicialSet.circle.{u} ⟶ triangleCell.{u} :=
  Under.homMk (pushout.inr (boundary.{u} 2).ι triangleAttachment) rfl

/-- 概要：cell 付着での円の包含は単射。
方針：標準境界包含の単射性を pushout へ移す。
規約：通常の単体集合の単射を使う。
使われ方：BF 1978 §2、HTT A.3.3。対角辺への制限の Kan fibration。 -/
instance triangleCellBoundary_mono : Mono triangleCellBoundary.{u}.right :=
  Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout (boundary.{u} 2).ι
    triangleAttachment)

/-- 概要：cell からの標準射はホーンを基点へ送る。
方針：pushout の関係式をホーンへ制限し、付着写像のホーン上の式を使う。
規約：ホーンは Λ[2,1]。
使われ方：Goerss–Jardine I §7。ホーンの cofiber からの降下条件。 -/
theorem triangleCellQuotient_horn : (horn.{u} 2 (1 : Fin 3)).ι ≫ triangleCellQuotient =
    toUnit (horn.{u} 2 (1 : Fin 3) : SSet.{u}) ≫ triangleCell.{u}.hom := by
  change (horn.{u} 2 (1 : Fin 3)).ι ≫ pushout.inl (boundary.{u} 2).ι triangleAttachment = _
  rw [show (horn.{u} 2 (1 : Fin 3)).ι =
      Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary 1 (1 : Fin 3)) ≫ (boundary.{u} 2).ι from rfl]
  rw [Category.assoc, pushout.condition, ← Category.assoc, boundaryFaceCollapse_horn]
  rfl

/-- 概要：ホーンの cofiber から cell の表示へ向かう実際の点つき射。
方針：cell からの標準射をホーンの商へ降ろす。
規約：商からの射の選択を使わない。
使われ方：Goerss–Jardine I §7。二つの相対三角形の表示の比較。 -/
def triangleDiskToCell : triangleDisk.{u} ⟶ triangleCell.{u} :=
  PointedObject.cofiberDesc (horn.{u} 2 (1 : Fin 3)).ι triangleCell.{u}
    triangleCellQuotient triangleCellQuotient_horn

/-- 概要：cell の付着写像はホーンの cofiber の対角辺の射と整合する。
方針：残る辺と他の二辺の各々で境界の式を比較する。
規約：境界上の厳密な等式。
使われ方：Goerss–Jardine I §7。cell の表示からホーンの cofiber へ降ろす。 -/
theorem triangleAttachment_diagonal :
    (boundary.{u} 2).ι ≫ triangleDiskQuotient =
      triangleAttachment ≫ triangleDiskDiagonal.{u}.right := by
  apply boundary.hom_ext
  intro j
  simp only [boundary.ι_ι_assoc]
  by_cases hj : j = (1 : Fin 3)
  · subst j
    rw [← Category.assoc, boundaryFaceCollapse_face]
    exact triangleDiskDiagonal_quotient.symm
  · rw [← Category.assoc, boundaryFaceCollapse_other_face _ _ _ hj,
      Category.assoc, Under.w triangleDiskDiagonal]
    rw [← horn.ι_ι (1 : Fin 3) j hj, Category.assoc,
      PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]

/-- 概要：cell の表示からホーンの cofiber への実際の点つき射。
方針：cell と円からの二つの標準射を pushout の普遍性で貼り合わせる。
規約：基点保存を円側から回収する。
使われ方：Goerss–Jardine I §7。対角辺の包含の cell による検査。 -/
def triangleCellToDisk : triangleCell.{u} ⟶ triangleDisk.{u} :=
  Under.homMk (pushout.desc triangleDiskQuotient triangleDiskDiagonal.right
    triangleAttachment_diagonal) (by
      change (PointedSimplicialSet.circle.{u}.hom ≫
        pushout.inr (boundary.{u} 2).ι triangleAttachment) ≫ _ = _
      rw [Category.assoc, pushout.inr_desc, Under.w triangleDiskDiagonal])

end

end SerrePositivity.KST.Spectra
