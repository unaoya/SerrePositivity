module
public import SerrePositivity.KST.ProExcision.CoefficientGroupLaws

/-!
# 単体的なイデアルの実列群と三角ブロック群

概要：各次数のイデアルの列群と実三角ブロック群を単体的群へ束ねる。
方針：係数群の恒等・合成法則を周囲の単体環の法則と組み合わせる。
規約：KST Lemma 4.16 の非可換な単体環上の実群模型。
使われ方：次数ごとの実帰納ホモトピーを対角の C(H) へ制限する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単体的イデアルの n 成分の加法群。
方針：各次数でイデアル内のベクトル群を取り、面・退化に係数写像を使う。
規約：KST Lemma 4.16 の M_{n,1}(I)。
使われ方：単体版の φ の始域。 -/
def SimplicialIdealData.columnGroup (I : SimplicialIdealData.{u}) (n : ℕ) : SimplicialObject GrpCat.{u} where
  obj k := GrpCat.of (Multiplicative (Fin n → I.ideal k))
  map {k l} φ := GrpCat.ofHom (idealVectorMap (I.ideal k) (I.ideal l) (Fin n) (I.ambient.map φ).hom
    (I.map_mem φ))
  map_id k := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro v
    change (fun i ↦ idealCoefficientAddHom (I.ideal k) (I.ideal k) (I.ambient.map (𝟙 k)).hom
      (I.map_mem (𝟙 k)) (v.toAdd i)) = v.toAdd
    funext i
    apply Subtype.ext
    change I.ambient.map (𝟙 k) (v.toAdd i : I.ambient.obj k) = (v.toAdd i : I.ambient.obj k)
    rw [I.ambient.map_id]
    rfl
  map_comp {k l s} φ ψ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro v
    change (fun i ↦ idealCoefficientAddHom (I.ideal k) (I.ideal s) (I.ambient.map (φ ≫ ψ)).hom
      (I.map_mem (φ ≫ ψ)) (v.toAdd i)) =
      (fun i ↦ idealCoefficientAddHom (I.ideal l) (I.ideal s) (I.ambient.map ψ).hom (I.map_mem ψ)
        (idealCoefficientAddHom (I.ideal k) (I.ideal l) (I.ambient.map φ).hom (I.map_mem φ) (v.toAdd i)))
    funext i
    apply Subtype.ext
    change I.ambient.map (φ ≫ ψ) (v.toAdd i : I.ambient.obj k) =
      I.ambient.map ψ (I.ambient.map φ (v.toAdd i : I.ambient.obj k))
    rw [I.ambient.map_comp]
    rfl

/-- 概要：単体的イデアルの実三角ブロック群。
方針：各次数で構成済みの実群を取り、係数写像の恒等・合成法則で束ねる。
規約：KST Lemma 4.16 の T_{n,m}(I)、非可換係数。
使われ方：帰納比較の単体的な値域 H。 -/
def SimplicialIdealData.triangularGroup (I : SimplicialIdealData.{u}) (n m : ℕ) : SimplicialObject GrpCat.{u} where
  obj k := GrpCat.of (triangularBlockGroup n m (I.ideal k))
  map {k l} φ := GrpCat.ofHom (triangularBlockGroupMap n m (I.ideal k) (I.ideal l) (I.ambient.map φ).hom
    (I.map_mem φ))
  map_id k := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    change I.ambient.map (𝟙 k) ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) (I.ambient.obj k)) i j) = _
    rw [I.ambient.map_id]
    rfl
  map_comp {k l s} φ ψ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    change I.ambient.map (φ ≫ ψ) ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) (I.ambient.obj k)) i j) =
      I.ambient.map ψ (I.ambient.map φ ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) (I.ambient.obj k)) i j))
    rw [I.ambient.map_comp]
    rfl

/-- 概要：零次の指定元による右乗法の列の単体的な群準同型。
方針：各次数の φ と指定元の自然性を使う。
規約：KST Lemma 4.16 の非可換版、φ(v)=va。
使われ方：単体版の実 m 次ホモトピーの始点。 -/
def SimplicialIdealData.rightColumnMap (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (n m : ℕ) : I.columnGroup n ⟶ I.triangularGroup n (m + 1) where
  app k := GrpCat.ofHom (lastRightColumnHom n m (I.ideal k) (I.vertexElement a k : I.ambient.obj k))
  naturality {k l} φ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro v
    exact lastRightColumnHom_functorial n m (I.ideal k) (I.ideal l) (I.ambient.map φ).hom (I.map_mem φ)
      (I.vertexElement a k : I.ambient.obj k) (I.vertexElement a l : I.ambient.obj l)
      (I.vertexElement_natural a φ) v

/-- 概要：二つの単体的群の間の自明な射。
方針：各次数で単位元への群準同型を使う。
規約：KST App. A の e。使われ方：単体版の帰納ホモトピーの終点。 -/
def simplicialGroupTrivialMap (M N : SimplicialObject GrpCat.{u}) : M ⟶ N where
  app k := GrpCat.ofHom (1 : M.obj k →* N.obj k)
  naturality {k l} φ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro v
    exact (N.map φ).hom.map_one.symm

end SerrePositivity.KST.ProExcision
