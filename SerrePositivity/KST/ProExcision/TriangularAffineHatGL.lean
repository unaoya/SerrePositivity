module
public import SerrePositivity.KST.ProExcision.SimplicialTriangularSplit
public import SerrePositivity.KST.ProExcision.TriangularSplitIntertwining

/-!
# 三角群から一般線形モノイドと列の実半直積への比較

概要：実三角群の分解の基底を ĜL へ入れ、最終列を保つ準同型を構成する。
方針：左上ブロックの実包含は列作用と可換なので半直積の誘導射を使う。
規約：KST Claim 4.15 の実値域、非単位非可換単体環。
使われ方：外部 ĜL と三角群を同時に比較する実射のファイバー側。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：非単位環の ĜL の係数イデアルの列群への実作用。
方針：全行列作用を ĜL の実表現に沿って制限する。
規約：KST Claim 4.15 の一般線形半直積。
使われ方：実三角行列の最終列の比較先。 -/
def NonUnitalSimplicialRing.hatGLColumnAction (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :=
  (I.standardIdeal.columnMatrixAction n).restrict (I.hatGLRepresentation n)

/-- 概要：三角群の左上ブロックと最終列を一般線形半直積へ送る実準同型。
方針：既証明の実分解へ、基底の三角群の ĜL への包含を後合成する。
規約：KST Claim 4.15、列成分はそのまま保つ。
使われ方：外部 ĜL を含む実比較の構成。 -/
def NonUnitalSimplicialRing.triangularAffineHatGLHom (I : NonUnitalSimplicialRing.{u})
    (n m q : ℕ) :
    triangularBlockGroup n (m + 1) (integerUnitizationIdeal (I.obj (op ⦋q⦌))) →*
      (simplicialActionProduct (I.hatGLColumnAction (n + m))).obj (op ⦋q⦌) := by
  letI := triangularColumnActionStructure n m (integerUnitizationIdeal (I.obj (op ⦋q⦌)))
  letI : MulDistribMulAction (I.hatGLSubmonoid (n + m) q)
      (Multiplicative (Fin (n + m) → integerUnitizationIdeal (I.obj (op ⦋q⦌)))) :=
    (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
  exact (actionProductMap
    (G := triangularBlockGroup n m (integerUnitizationIdeal (I.obj (op ⦋q⦌))))
    (H := Multiplicative (Fin (n + m) → integerUnitizationIdeal (I.obj (op ⦋q⦌))))
    (G' := I.hatGLSubmonoid (n + m) q)
    (H' := Multiplicative (Fin (n + m) → integerUnitizationIdeal (I.obj (op ⦋q⦌))))
    (I.triangularHatGLHom n m q) (MonoidHom.id _)
    (fun _ _ ↦ rfl)).comp
      (triangularBlockAffineSplit n m (integerUnitizationIdeal (I.obj (op ⦋q⦌))))

/-- 概要：三角群から一般線形半直積への実比較は単体的。
方針：左上ブロックの係数自然性と最終列の係数自然性を比較する。
規約：KST Claim 4.15、実自然変換。使われ方：相対 bar の実値域射。 -/
def NonUnitalSimplicialRing.triangularAffineHatGLMap (I : NonUnitalSimplicialRing.{u})
    (n m : ℕ) :
    I.standardIdeal.triangularGroup n (m + 1) ⋙ forget₂ GrpCat MonCat ⟶
      simplicialActionProduct (I.hatGLColumnAction (n + m)) where
  app k := by
    rcases k with ⟨⟨q⟩⟩
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    exact MonCat.ofHom (I.triangularAffineHatGLHom n m q)
  naturality {k l} f := by
    rcases k with ⟨⟨p⟩⟩
    rcases l with ⟨⟨q⟩⟩
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋p⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply ActionProduct.ext
    · apply Subtype.ext
      rfl
    · rfl

end SerrePositivity.KST.ProExcision
