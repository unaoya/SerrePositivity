module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLBlock
public import SerrePositivity.KST.ProExcision.ActionProductLift
public import SerrePositivity.KST.ProExcision.TriangularHatGL

/-!
# 外部 ĜL と三角群の実ブロック積

概要：ĜL_n と T_{n,m} の半直積から ĜL_{n+m} への実射を構成する。
方針：三角行列を先に、外部行列の単位ブロック和を後に掛ける。
規約：KST Claim 4.15 の G_{n,m}(I) の実包含。外部行列は π₀ でのみ可逆でよい。
使われ方：低次相対零化を一般線形モノイドへ移す実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実三角群の行列作用は単位ブロック和との交換則を満たす。
方針：1+B(t−1) の式と (t−1)B=t−1 の右吸収を使う。
規約：KST Claim 4.15、非可逆な一般行列に対して成立。
使われ方：実半直積から行列積への準同型の構成。 -/
lemma triangularBlockMatrixAction_intertwining {R : Type u} [Ring R]
    (n m : ℕ) (J : TwoSidedIdeal R) (M : Matrix (Fin n) (Fin n) R)
    (t : triangularBlockGroup n m J) :
    (triangularBlockMatrixAction n m J M t).val.val * firstBlockMatrix n m M =
      firstBlockMatrix n m M * t.val.val := by
  change (triangularBlockMatrixEnd n m J M t).val.val * _ = _
  rw [triangularBlockMatrixEnd_val, add_mul, one_mul, mul_assoc,
    blockPattern_firstBlock_right_absorbed n m J M _ t.property.1]
  rw [mul_sub, mul_one, add_sub_cancel]

/-- 概要：外部 ĜL と実三角群の半直積の単体的作用。
方針：ĜL の全行列表現に沿って構成済みの三角群の作用を制限する。
規約：KST Claim 4.15 の G_{n,m}(I)。使われ方：実ブロック積の定義域。 -/
def NonUnitalSimplicialRing.triangularGLAction (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :=
  (I.standardIdeal.triangularMatrixAction n m).restrict (I.hatGLRepresentation n)

/-- 概要：外部 ĜL と三角群の各次数の実ブロック積準同型。
方針：実包含と単位ブロック和を交換則による半直積の普遍写像へ渡す。
規約：KST Claim 4.15、次数ごとの逆元を要求しない。
使われ方：G_{n,m}(I) から ĜL_{n+m}(I) への実比較。 -/
def NonUnitalSimplicialRing.triangularGLProductHom (I : NonUnitalSimplicialRing.{u})
    (n m : ℕ) (k : SimplexCategoryᵒᵖ) :
    (simplicialActionProduct (I.triangularGLAction n m)).obj k →*
      (I.hatGL (n + m)).obj k := by
  rcases k with ⟨⟨q⟩⟩
  letI := (I.triangularGLAction n m).actionStructure (op ⦋q⦌)
  exact actionProductLift (I.hatGLBlockHom n m q)
    (I.triangularHatGLHom n m q) (by
      intro g t
      apply Subtype.ext
      exact triangularBlockMatrixAction_intertwining n m _ g.val t)

/-- 概要：外部 ĜL と三角群の実ブロック積は単体的。
方針：実行列積と単位ブロック和の係数自然性を比較する。
規約：KST Claim 4.15、実モノイド間の自然変換。
使われ方：相対 bar 比較の実値域射。 -/
def NonUnitalSimplicialRing.triangularGLProductMap (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    simplicialActionProduct (I.triangularGLAction n m) ⟶ I.hatGL (n + m) where
  app k := by
    letI := (I.triangularGLAction n m).actionStructure k
    exact MonCat.ofHom (I.triangularGLProductHom n m k)
  naturality {k l} f := by
    rcases k with ⟨⟨p⟩⟩
    rcases l with ⟨⟨q⟩⟩
    letI := (I.triangularGLAction n m).actionStructure (op ⦋p⦌)
    letI := (I.triangularGLAction n m).actionStructure (op ⦋q⦌)
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ActionProduct (I.hatGLSubmonoid n p)
      (triangularBlockGroup n m (integerUnitizationIdeal (I.obj (op ⦋p⦌)))) at x
    apply Subtype.ext
    change ((integerUnitizationMap (I.map f)).mapMatrix x.fiber.val.val) *
        firstBlockMatrix n m ((integerUnitizationMap (I.map f)).mapMatrix x.base.val) =
      (integerUnitizationMap (I.map f)).mapMatrix
        (x.fiber.val.val * firstBlockMatrix n m x.base.val)
    rw [map_mul]
    rw [show (integerUnitizationMap (I.map f)).mapMatrix (firstBlockMatrix n m x.base.val) =
        firstBlockMatrix n m ((integerUnitizationMap (I.map f)).mapMatrix x.base.val)
      from firstBlockMatrix_coefficient_map n m _ x.base.val]

end SerrePositivity.KST.ProExcision
