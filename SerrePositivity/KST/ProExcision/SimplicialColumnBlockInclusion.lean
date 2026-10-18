module
public import SerrePositivity.KST.ProExcision.IdealColumnBlockInclusion
public import SerrePositivity.KST.ProExcision.ActionOverMorphisms

/-!
# 列のブロック包含と通常の半直積の単体的安定化

概要：零埋め列と基底の単位ブロック和による通常の rank の安定化を構成する。
方針：係数写像による零埋めの自然性と実行列作用の同変性を束ねる。
規約：KST Claim 4.15・Proposition 4.14、右乗法なしの通常の安定化。
使われ方：有限 rank の相対 bar 項の実順序列。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単体的イデアル内の列の零埋め包含。
方針：各次数の加法準同型を取り、係数写像による成分公式を比較する。
規約：KST Claim 4.15。使われ方：相対半直積の通常の rank 安定化。 -/
def SimplicialIdealData.columnBlockMap (I : SimplicialIdealData.{u}) (n m : ℕ) :
    I.columnGroup n ⋙ forget₂ GrpCat MonCat ⟶ I.columnGroup (n + m) ⋙ forget₂ GrpCat MonCat where
  app k := MonCat.ofHom (columnBlockInclusion (I.ideal k) n m).toMultiplicative
  naturality {k l} f := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro v
    symm
    change (fun i ↦ idealCoefficientAddHom (I.ideal k) (I.ideal l) (I.ambient.map f).hom
        (I.map_mem f) (columnBlockInclusion (I.ideal k) n m v.toAdd i)) =
      columnBlockInclusion (I.ideal l) n m
        (fun i ↦ idealCoefficientAddHom (I.ideal k) (I.ideal l) (I.ambient.map f).hom
          (I.map_mem f) (v.toAdd i))
    funext i
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
    cases i with
    | inl i => simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
    | inr i =>
      simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right, map_zero]

/-- 概要：通常の基底と列のブロック包含は作用に同変な実単体射。
方針：基底の単位ブロック和、列の零埋め、実行列作用の同変性を束ねる。
規約：KST Proposition 4.14 の安定化、右乗法は含まない。
使われ方：相対項の有限 rank の順序列。 -/
def NonUnitalSimplicialRing.columnBlockOverHom (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    SimplicialActionOverHom (I.hatGLColumnAction n) (I.hatGLColumnAction (n + m)) where
  base := I.hatGLBlockMap n m
  fiber := I.standardIdeal.columnBlockMap n m
  equivariant k g v := by
    rcases k with ⟨⟨q⟩⟩
    exact (idealColumnBlockInclusion_equivariant _ n m g.val v).symm

end SerrePositivity.KST.ProExcision
