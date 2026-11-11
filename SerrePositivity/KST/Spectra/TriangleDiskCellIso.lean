module

public import SerrePositivity.KST.Spectra.TriangleDiskCell
public import SerrePositivity.KST.Spectra.PointedMappingNaturality

/-!
概要：相対三角形の cell 表示との同型と対角辺の単射性。
方針：二つの普遍性で逆写像を検査し、境界包含の単射性を移す。
規約：同型は通常の点つき単体集合の厳密な同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。対角辺への写像空間の Kan fibration。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cell の円の包含を区間へ制限すると cell の対角辺。
方針：pushout の関係式を残る面へ制限する。
規約：辺の向きはホーンの cofiber の対角辺と同じ。
使われ方：Goerss–Jardine I §7。二つの表示の比較の円側の検査。 -/
@[reassoc (attr := simp)]
theorem triangleCellBoundary_quotient :
    PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ triangleCellBoundary.{u}.right =
      stdSimplex.δ (1 : Fin 3) ≫ triangleCellQuotient := by
  change PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
    pushout.inr (boundary.{u} 2).ι triangleAttachment = _
  rw [← boundaryFaceCollapse_face 1 (1 : Fin 3), Category.assoc,
    ← pushout.condition, ← Category.assoc, boundary.ι_ι]

/-- 概要：ホーンの cofiber から cell 表示への射は対角辺を円の包含へ送る。
方針：円の商の普遍性で区間上の計算へ戻す。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7。cell 表示の同型の円側の条件。 -/
@[reassoc (attr := simp)]
theorem triangleDiskDiagonal_toCell :
    triangleDiskDiagonal.{u} ≫ triangleDiskToCell = triangleCellBoundary := by
  apply PointedObject.cofiber_hom_ext (boundary.{u} 1).ι
  rw [Under.comp_right, triangleDiskDiagonal_quotient_assoc]
  have hq : triangleDiskQuotient.{u} ≫ triangleDiskToCell.{u}.right =
      triangleCellQuotient.{u} := PointedObject.cofiberQuotient_desc
        (horn.{u} 2 (1 : Fin 3)).ι triangleCell.{u} triangleCellQuotient triangleCellQuotient_horn
  rw [hq]
  exact triangleCellBoundary_quotient.symm

/-- 概要：cell 表示からホーンの cofiber への射を円へ制限すると対角辺。
方針：pushout の円側の標準射で計算する。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7。対角辺の単射性を cell 表示から戻す。 -/
@[reassoc (attr := simp)]
theorem triangleCellBoundary_toDisk :
    triangleCellBoundary.{u} ≫ triangleCellToDisk = triangleDiskDiagonal := by
  apply Under.UnderMorphism.ext
  exact pushout.inr_desc _ _ _

/-- 概要：相対三角形の cell 表示からホーンの cofiber への厳密な同型。
方針：片方の逆条件は pushout の二辺で、他方は cofiber の商上で検査する。
規約：点つき単体集合の通常の同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2。対角辺の包含の単射性の移送。 -/
def triangleCellIso : triangleCell.{u} ≅ triangleDisk.{u} where
  hom := triangleCellToDisk
  inv := triangleDiskToCell
  hom_inv_id := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · change (pushout.inl (boundary.{u} 2).ι triangleAttachment ≫
        (pushout.desc triangleDiskQuotient triangleDiskDiagonal.right
          triangleAttachment_diagonal)) ≫ triangleDiskToCell.right = _
      rw [pushout.inl_desc]
      exact PointedObject.cofiberQuotient_desc _ _ _ _
    · change triangleCellBoundary.{u}.right ≫
        (triangleCellToDisk.right ≫ triangleDiskToCell.right) = triangleCellBoundary.right
      rw [← Under.comp_right, ← Under.comp_right, ← Category.assoc,
        triangleCellBoundary_toDisk, triangleDiskDiagonal_toCell]
  inv_hom_id := by
    apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
    rw [Under.comp_right]
    change PointedObject.cofiberQuotient (horn.{u} 2 (1 : Fin 3)).ι ≫
      (PointedObject.cofiberDesc _ _ _ _).right ≫ triangleCellToDisk.right = _
    rw [PointedObject.cofiberQuotient_desc_assoc]
    exact pushout.inl_desc _ _ _

/-- 概要：相対三角形の対角辺の円からの射は単射。
方針：cell 表示の円の包含と厳密な同型を合成する。
規約：Kan 置換を使わず実際の単体集合の単射を示す。
使われ方：Goerss–Jardine I §7、HTT A.3.3。対角辺への制限の Kan fibration。 -/
instance triangleDiskDiagonal_mono : Mono triangleDiskDiagonal.{u}.right := by
  have h : triangleDiskDiagonal.{u}.right = triangleCellBoundary.right ≫
      (PointedSimplicialSet.forget.mapIso triangleCellIso).hom := by
    exact (congrArg Under.Hom.right triangleCellBoundary_toDisk).symm
  rw [h]
  infer_instance

/-- 概要：相対三角形の Kan 値写像空間から共通の対角 loop への制限は Kan fibration。
方針：対角辺の単射性と指数版 pushout-product の充填を使う。
規約：標的 Y だけに Kan 性を要求する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。正方形の二つの三角形の差を計算する。 -/
instance triangleDisk_restriction_fibration (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Fibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed triangleDiskDiagonal.{u} Y).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _ Y

end

end SerrePositivity.KST.Spectra
