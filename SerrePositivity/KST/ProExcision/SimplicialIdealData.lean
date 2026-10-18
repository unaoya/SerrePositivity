module
public import SerrePositivity.KST.ProExcision.DiagonalGroupBar
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# 単体環内の両側イデアルと零次の指定元

概要：単体的な単位環の両側イデアルの族と、零次の元の各次数への移送を明示する。
方針：面・退化によるイデアルの保存を数学的データとして持ち、指定元は唯一の [n]→[0] で移す。
規約：KST Proposition 4.14・Lemma 4.16 の非単位環を単位化の核イデアルで表す模型。
使われ方：次数ごとの実群と実ホモトピーを単体的に束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単体的単位環の中で面・退化が保つ両側イデアルの族。
方針：周囲環と各次数のイデアルおよび所属の保存だけを保持する。
規約：KST 4.14・4.16 の非可換な非単位単体環の理想模型。ホモトピーの結論は含めない。
使われ方：実三角ブロック群の単体化。 -/
structure SimplicialIdealData where
  ambient : SimplicialObject RingCat.{u}
  ideal (k : SimplexCategoryᵒᵖ) : TwoSidedIdeal (ambient.obj k)
  map_mem {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) (x : ambient.obj k) :
    x ∈ ideal k → ambient.map φ x ∈ ideal l

/-- 概要：零次の元を次数 k へ送る標準の単体射。
方針：唯一の k.unop→[0] を反対にする。
規約：KST 4.16 の a∈I₀。使われ方：各次数での補助元の定義。 -/
def simplexVertexMap (k : SimplexCategoryᵒᵖ) : op ⦋0⦌ ⟶ k :=
  (SimplexCategory.const k.unop ⦋0⦌ 0).op

/-- 概要：零次からの標準の単体射は全ての面・退化に可換。
方針：標的が [0] の射の一意性を使う。
規約：KST 4.16。使われ方：指定元の自然性。 -/
lemma simplexVertexMap_comp {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) :
    simplexVertexMap k ≫ φ = simplexVertexMap l := by
  change (φ.unop ≫ SimplexCategory.const k.unop ⦋0⦌ 0).op =
    (SimplexCategory.const l.unop ⦋0⦌ 0).op
  congr 1

/-- 概要：イデアルの零次の元を任意の次数のイデアルへ移す。
方針：周囲の単体環の標準射とイデアルの保存を使う。
規約：KST 4.16 の各次数の a。使われ方：実帰納ホモトピーの次数ごとの入力。 -/
def SimplicialIdealData.vertexElement (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (k : SimplexCategoryᵒᵖ) : I.ideal k :=
  ⟨I.ambient.map (simplexVertexMap k) (a : I.ambient.obj (op ⦋0⦌)),
    I.map_mem _ _ a.property⟩

/-- 概要：指定元の各次数への移送は周囲の単体環の射に自然。
方針：単体環の合成保存と標準の頂点射の自然性を使う。
規約：KST 4.16 の (I,a) の関手性。
使われ方：係数次数間の実群ホモトピーの自然性に渡す。 -/
lemma SimplicialIdealData.vertexElement_natural (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) :
    I.ambient.map φ (I.vertexElement a k : I.ambient.obj k) =
      (I.vertexElement a l : I.ambient.obj l) := by
  have h := congrArg (fun f : I.ambient.obj (op ⦋0⦌) ⟶ I.ambient.obj l ↦
    f (a : I.ambient.obj (op ⦋0⦌))) (I.ambient.map_comp (simplexVertexMap k) φ).symm
  rw [simplexVertexMap_comp] at h
  exact h

end SerrePositivity.KST.ProExcision
