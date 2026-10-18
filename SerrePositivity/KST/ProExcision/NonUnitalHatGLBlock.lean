module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGL

/-!
# 非単位環の ĜL のブロック安定化

概要：単位ブロックを付け加える実準同型を非単位環の ĜL 上で構成する。
方針：成分行列と整数射影がブロック和に自然であることを使う。
規約：KST Claim 4.15、一般の有限補助 rank m を許す。
使われ方：外部 ĜL_n の ĜL_{n+m} への実基底射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単位ブロックとの和を行列のモノイド準同型にする。
方針：既証明の単位・積の公式を使う。
規約：KST Claim 4.15、非可換な係数環。
使われ方：π₀ の単位性をブロック和へ移す。 -/
def firstBlockMatrixHom (R : Type u) [Ring R] (n m : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin (n + m)) (Fin (n + m)) R where
  toFun := firstBlockMatrix n m
  map_one' := firstBlockMatrix_one n m
  map_mul' := firstBlockMatrix_mul n m

/-- 概要：非単位環の ĜL の各次数のブロック安定化。
方針：成分での単位性をブロック和で保ち、整数射影の恒等条件も保つ。
規約：KST Claim 4.15、次数ごとの逆元は要求しない。
使われ方：実半直積比較の基底射。 -/
def NonUnitalSimplicialRing.hatGLBlockHom (I : NonUnitalSimplicialRing.{u})
    (n m q : ℕ) : I.hatGLSubmonoid n q →* I.hatGLSubmonoid (n + m) q where
  toFun M := ⟨firstBlockMatrix n m M.val, by
    constructor
    · change IsUnit ((Comparison.SimplicialRing.simplexToComponents I.standardIdeal.ambient q).mapMatrix
        (firstBlockMatrix n m M.val))
      rw [show (Comparison.SimplicialRing.simplexToComponents I.standardIdeal.ambient q).mapMatrix
          (firstBlockMatrix n m M.val) =
          firstBlockMatrix n m (Comparison.matrixToComponents I.standardIdeal.ambient n q M.val)
        from firstBlockMatrix_coefficient_map n m _ M.val]
      exact M.property.1.map (firstBlockMatrixHom _ n m)
    · rw [show (Unitization.fstHom ℤ (I.obj (op ⦋q⦌))).mapMatrix
          (firstBlockMatrix n m M.val) =
          firstBlockMatrix n m ((Unitization.fstHom ℤ (I.obj (op ⦋q⦌))).mapMatrix M.val)
        from firstBlockMatrix_coefficient_map n m _ M.val]
      rw [M.property.2, firstBlockMatrix_one]⟩
  map_one' := Subtype.ext (firstBlockMatrix_one n m)
  map_mul' M N := Subtype.ext (firstBlockMatrix_mul n m M.val N.val)

/-- 概要：非単位環の ĜL のブロック安定化は単体的。
方針：ブロック和と面・退化の係数写像の可換性を使う。
規約：KST Claim 4.15。使われ方：相対 bar 比較の基底の単体射。 -/
def NonUnitalSimplicialRing.hatGLBlockMap (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    I.hatGL n ⟶ I.hatGL (n + m) where
  app k := MonCat.ofHom (I.hatGLBlockHom n m k.unop.len)
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    apply Subtype.ext
    exact (firstBlockMatrix_coefficient_map n m (integerUnitizationMap (I.map f)) M.val).symm

end SerrePositivity.KST.ProExcision
