module
public import SerrePositivity.KST.ProExcision.TriangularAffineHatGL

/-!
# Claim 4.15 の実半直積への因子化

概要：ĜL_n と T_{n,m+1} の実半直積を ĜL_{n+m} と列群の半直積へ送る。
方針：三角群の最終列分解と外部行列の単位ブロック和を、二成分の交換則で組み合わせる。
規約：KST Claim 4.15、非単位非可換な I。次数ごとの ĜL の逆元は使わない。
使われ方：A.4 の相対零写像を原典の有限 rank の相対写像へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：Claim 4.15 の値域へ送る各次数の実準同型。
方針：基底を単位ブロック和、ファイバーを三角群の実分解で送り、交換則を証明する。
規約：KST Claim 4.15、相対零化をこの定義の仮定にしない。
使われ方：実相対写像の因子化。 -/
def claim415FactorizationHom (I : NonUnitalSimplicialRing.{u}) (n m q : ℕ) :
    (simplicialActionProduct (I.triangularGLAction n (m + 1))).obj (op ⦋q⦌) →*
      (simplicialActionProduct (I.hatGLColumnAction (n + m))).obj (op ⦋q⦌) := by
  let J := integerUnitizationIdeal (I.obj (op ⦋q⦌))
  letI : MulDistribMulAction (I.hatGLSubmonoid n q) (triangularBlockGroup n (m + 1) J) :=
    (I.triangularGLAction n (m + 1)).actionStructure (op ⦋q⦌)
  letI : MulDistribMulAction (I.hatGLSubmonoid (n + m) q)
      (Multiplicative (Fin (n + m) → J)) :=
    (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
  let f : I.hatGLSubmonoid n q →*
      ActionProduct (I.hatGLSubmonoid (n + m) q) (Multiplicative (Fin (n + m) → J)) :=
    (actionProductSection (G := I.hatGLSubmonoid (n + m) q) (H := Multiplicative (Fin (n + m) → J))).comp (I.hatGLBlockHom n m q)
  exact actionProductLift (G := I.hatGLSubmonoid n q)
    (H := triangularBlockGroup n (m + 1) J)
    (K := ActionProduct (I.hatGLSubmonoid (n + m) q) (Multiplicative (Fin (n + m) → J))) f (I.triangularAffineHatGLHom n m q) (by
    intro g t
    apply ActionProduct.ext
    · apply Subtype.ext
      exact triangularAction_dropLast_intertwining n m J g.val t
    · change Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J
          (triangularBlockMatrixAction n (m + 1) J g.val t)) *
          idealMatrixAction (n + m) J
            (matrixDropLast (triangularBlockMatrixAction n (m + 1) J g.val t).val.val) 1 =
        1 * idealMatrixAction (n + m) J (firstBlockMatrix n m g.val)
          (Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J t))
      rw [map_one, mul_one, one_mul]
      change triangularBlockGroupLastColumn n m J
          (triangularBlockMatrixAction n (m + 1) J g.val t) =
        (idealMatrixAction (n + m) J (firstBlockMatrix n m g.val)
          (Multiplicative.ofAdd (triangularBlockGroupLastColumn n m J t))).toAdd
      funext i
      apply Subtype.ext
      exact congrFun (triangularAction_lastColumn n m J g.val t) i)

/-- 概要：実因子化の基底成分は左上ブロックと単位ブロック和の積。
方針：半直積からの準同型の定義を評価する。
規約：KST Claim 4.15。使われ方：単体的自然性の成分比較。 -/
lemma claim415FactorizationHom_base (I : NonUnitalSimplicialRing.{u}) (n m q : ℕ)
    (x : ActionProduct (I.hatGLSubmonoid n q)
      (triangularBlockGroup n (m + 1) (integerUnitizationIdeal (I.obj (op ⦋q⦌))))) :
    (claim415FactorizationHom I n m q x).base.val =
      matrixDropLast x.fiber.val.val * firstBlockMatrix n m x.base.val := rfl

/-- 概要：実因子化の列成分は三角群の最終列そのもの。
方針：半直積の基底包含の列成分は単位なので作用の単位保存で消す。
規約：KST Claim 4.15。使われ方：単体的自然性と右乗法の比較。 -/
lemma claim415FactorizationHom_fiber (I : NonUnitalSimplicialRing.{u}) (n m q : ℕ)
    (x : ActionProduct (I.hatGLSubmonoid n q)
      (triangularBlockGroup n (m + 1) (integerUnitizationIdeal (I.obj (op ⦋q⦌))))) :
    (claim415FactorizationHom I n m q x).fiber =
      Multiplicative.ofAdd (triangularBlockGroupLastColumn n m
        (integerUnitizationIdeal (I.obj (op ⦋q⦌))) x.fiber) := by
  change Multiplicative.ofAdd (triangularBlockGroupLastColumn n m _ x.fiber) *
      idealMatrixAction (n + m) _ (matrixDropLast x.fiber.val.val) 1 = _
  rw [map_one, mul_one]

/-- 概要：Claim 4.15 の値域への実因子化は単体的。
方針：基底は係数写像の積保存、列は最終列の自然性で比較する。
規約：KST Claim 4.15、実自然変換。使われ方：相対 bar 項への降下。 -/
def claim415FactorizationMap (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    simplicialActionProduct (I.triangularGLAction n (m + 1)) ⟶
      simplicialActionProduct (I.hatGLColumnAction (n + m)) where
  app k := by
    rcases k with ⟨⟨q⟩⟩
    letI := (I.triangularGLAction n (m + 1)).actionStructure (op ⦋q⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    exact MonCat.ofHom (claim415FactorizationHom I n m q)
  naturality {k l} f := by
    rcases k with ⟨⟨p⟩⟩
    rcases l with ⟨⟨q⟩⟩
    letI := (I.triangularGLAction n (m + 1)).actionStructure (op ⦋p⦌)
    letI := (I.triangularGLAction n (m + 1)).actionStructure (op ⦋q⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋p⦌)
    letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ActionProduct (I.hatGLSubmonoid n p)
      (triangularBlockGroup n (m + 1) (integerUnitizationIdeal (I.obj (op ⦋p⦌)))) at x
    apply ActionProduct.ext
    · apply Subtype.ext
      change (claim415FactorizationHom I n m q
          ((simplicialActionProduct (I.triangularGLAction n (m + 1))).map f x)).base.val =
        (integerUnitizationMap (I.map f)).mapMatrix (claim415FactorizationHom I n m p x).base.val
      rw [claim415FactorizationHom_base, claim415FactorizationHom_base, map_mul]
      rw [show (integerUnitizationMap (I.map f)).mapMatrix (firstBlockMatrix n m x.base.val) =
          firstBlockMatrix n m ((integerUnitizationMap (I.map f)).mapMatrix x.base.val)
        from firstBlockMatrix_coefficient_map n m _ x.base.val]
      rfl
    · change (claim415FactorizationHom I n m q
          ((simplicialActionProduct (I.triangularGLAction n (m + 1))).map f x)).fiber =
        idealVectorMap _ _ (Fin (n + m)) (integerUnitizationMap (I.map f))
          (integerUnitizationMap_ideal (I.map f)) (claim415FactorizationHom I n m p x).fiber
      rw [claim415FactorizationHom_fiber, claim415FactorizationHom_fiber]
      rfl

end SerrePositivity.KST.ProExcision
