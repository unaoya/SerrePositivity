module

public import SerrePositivity.KST.Spectra.AnodyneCofiberSource
public import SerrePositivity.KST.Spectra.PathContractibility

/-!
概要：相対三角形の共通の対角辺を円からの射として表示する。
方針：ホーンの全頂点が基点へ潰れることを使って、残る辺を円へ降ろす。
規約：三角形の二辺はホーンに含まれ、残る辺の添字は 1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。正方形の二つの三角形の共通辺。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準三角形から相対三角形への実際の商写像。
方針：内側のホーンを潰す cofiber の標準射を使う。
規約：ホーンは Λ[2,1]。
使われ方：Goerss–Jardine I §7。正方形の三角形からの制限。 -/
abbrev triangleDiskQuotient : (Δ[2] : SSet.{u}) ⟶ triangleDisk.{u}.right :=
  PointedObject.cofiberQuotient (horn.{u} 2 (1 : Fin 3)).ι

/-- 概要：三角形の全ての頂点は相対三角形の基点へ写る。
方針：ホーンの零単体は標準三角形の全頂点を含む。
規約：三頂点に個別の選択はしない。
使われ方：Goerss–Jardine I §7。対角辺の二端点が基点となる条件。 -/
theorem triangleDiskQuotient_vertex (v : (Δ[2] : SSet.{u}) _⦋0⦌) :
    triangleDiskQuotient.app _ v = triangleDisk.{u}.basepoint := by
  have hv : v ∈ (horn.{u} 2 (1 : Fin 3)).obj _ := by
    rw [horn_obj_zero]
    trivial
  have h := congrArg (fun f : (horn.{u} 2 (1 : Fin 3) : SSet.{u}) ⟶ triangleDisk.{u}.right =>
    f.app _ ⟨v, hv⟩) (PointedObject.cofiberQuotient_condition (horn.{u} 2 (1 : Fin 3)).ι)
  exact h

/-- 概要：相対三角形の残る対角辺の二端点は基点へ写る。
方針：境界の二つの頂点で商写像の頂点の計算を使う。
規約：残る辺は δ₁。
使われ方：Goerss–Jardine I §7。対角辺の円への降下条件。 -/
theorem triangleDisk_diagonal_boundary :
    (boundary.{u} 1).ι ≫ stdSimplex.δ (1 : Fin 3) ≫ triangleDiskQuotient =
      toUnit (boundary.{u} 1 : SSet.{u}) ≫ triangleDisk.{u}.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]
  apply boundary.hom_ext
  intro j
  simp only [boundary.ι_ι_assoc, SSet.comp_const]
  fin_cases j
  · change stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) ≫
      triangleDiskQuotient = SSet.const triangleDisk.{u}.basepoint
    erw [stdSimplex.δ_zero_eq_const, SSet.const_comp]
    change SSet.const (triangleDiskQuotient.app _ _) = SSet.const triangleDisk.{u}.basepoint
    rw [triangleDiskQuotient_vertex]
  · change stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) ≫
      triangleDiskQuotient = SSet.const triangleDisk.{u}.basepoint
    erw [stdSimplex.δ_one_eq_const, SSet.const_comp]
    change SSet.const (triangleDiskQuotient.app _ _) = SSet.const triangleDisk.{u}.basepoint
    rw [triangleDiskQuotient_vertex]

/-- 概要：相対三角形の対角辺を与える円からの点つき射。
方針：二端点の基点条件により境界を潰した商へ降ろす。
規約：通常の単体的な円を使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の共通の対角 loop。 -/
def triangleDiskDiagonal : PointedSimplicialSet.circle.{u} ⟶ triangleDisk.{u} :=
  PointedObject.cofiberDesc (boundary.{u} 1).ι triangleDisk.{u}
    (stdSimplex.δ (1 : Fin 3) ≫ triangleDiskQuotient) triangleDisk_diagonal_boundary

/-- 概要：対角辺の円への降下は区間上で元の対角辺に一致する。
方針：cofiber の降下の標準射での式を使う。
規約：実際の単体集合の射の厳密な等式。
使われ方：Goerss–Jardine I §7。三角形の写像空間の共通の底の検査。 -/
@[reassoc (attr := simp)]
theorem triangleDiskDiagonal_quotient :
    PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫ triangleDiskDiagonal.right =
      stdSimplex.δ (1 : Fin 3) ≫ triangleDiskQuotient :=
  PointedObject.cofiberQuotient_desc _ _ _ _

end

end SerrePositivity.KST.Spectra
