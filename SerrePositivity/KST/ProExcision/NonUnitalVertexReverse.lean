module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialReverse
public import SerrePositivity.KST.ProExcision.Prop414

/-!
# 非単位環の指定元と反転・反対環の整合

概要：零次の指定元の全次数への像が係数反転と反対環に保たれることを証明する。
方針：標的が [0] の単体射の一意性を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：行側乗法と列側乗法の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：零次の指定元の実非単位単体環の任意の次数への像。
方針：標準の [n]→[0] による反変係数写像を使う。
規約：KST Proposition 4.14。使われ方：次数ごとの中心性・単射性と乗法。 -/
def NonUnitalSimplicialRing.vertexValue (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (k : SimplexCategoryᵒᵖ) : I.obj k :=
  I.map (simplexVertexMap k) a

/-- 概要：係数の順序反転は標準の頂点射を保つ。
方針：[0] を標的とする単体射の一意性を使う。
規約：SW92 §1.2。使われ方：反転した指定元の全次数での同定。 -/
lemma simplexVertexMap_rev (k : SimplexCategoryᵒᵖ) :
    (SimplexCategory.rev.map (simplexVertexMap k).unop).op = simplexVertexMap k := by
  congr 1

/-- 概要：反転した反対係数環の指定元の像は元の像の反対元。
方針：標準の頂点射の rev 不変性を実係数写像に適用する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：列の右乗法と行の左乗法の係数の整合。 -/
lemma NonUnitalSimplicialRing.reverseOpposite_vertexValue
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (k : SimplexCategoryᵒᵖ) :
    I.reverseOpposite.vertexValue (MulOpposite.op a) k = MulOpposite.op (I.vertexValue a k) := by
  change MulOpposite.op (I.map (SimplexCategory.rev.map (simplexVertexMap k).unop).op a) = _
  rw [simplexVertexMap_rev]
  rfl

/-- 概要：標準単位化の指定元は元の非単位環の指定元の標準包含。
方針：実単位化写像が元の環の包含と可換であることを使う。
規約：KST Proposition 4.14。使われ方：実核イデアル模型の乗法の係数。 -/
lemma NonUnitalSimplicialRing.standardVertexElement_coe
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (k : SimplexCategoryᵒᵖ) :
    (I.standardIdeal.vertexElement (I.standardElement a) k).val =
      (I.vertexValue a k : Unitization ℤ (I.obj k)) :=
  integerUnitizationMap_inr (I.map (simplexVertexMap k)) a

/-- 概要：中心性は反対係数環で保存される。
方針：全ての反対元を unop し、元の中心性の等式を逆に読む。
規約：KST Proposition 4.14 の非可換版。
使われ方：行側へ普遍的な列側補題を適用する際の仮定。 -/
lemma isCentralElement_op {J : Type u} [NonUnitalRing J] {a : J}
    (ha : IsCentralElement a) : IsCentralElement (MulOpposite.op a) := by
  intro x
  apply MulOpposite.unop_injective
  exact (ha (MulOpposite.unop x)).symm

end SerrePositivity.KST.ProExcision
