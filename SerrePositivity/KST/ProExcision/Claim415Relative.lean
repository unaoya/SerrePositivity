module
public import SerrePositivity.KST.ProExcision.Claim415Factorization
public import SerrePositivity.KST.ProExcision.RelativeBarPairs
public import SerrePositivity.KST.ProExcision.NonUnitalLemma416Relative

/-!
# Claim 4.15 の実相対写像の因子化と零化

概要：外部 ĜL と三角群の実比較を相対 bar 項に降ろす。
方針：基底の標準包含との可換性を証明し、A.4 による実零写像を後合成する。
規約：KST Claim 4.15。H_* の模型は K-L2 の明示的引数。
使われ方：右乗法による有限 rank の相対写像の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：実因子化は基底の標準包含とブロック安定化に関して可換。
方針：基底は恒等三角行列の左上ブロック、列はその零の最終列として計算する。
規約：KST Claim 4.15。使われ方：相対項への降下。 -/
lemma claim415FactorizationMap_section (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    simplicialActionProductSection (I.triangularGLAction n (m + 1)) ≫
        claim415FactorizationMap I n m =
      I.hatGLBlockMap n m ≫ simplicialActionProductSection (I.hatGLColumnAction (n + m)) := by
  apply NatTrans.ext
  funext k
  rcases k with ⟨⟨q⟩⟩
  letI := (I.triangularGLAction n (m + 1)).actionStructure (op ⦋q⦌)
  letI := (I.hatGLColumnAction (n + m)).actionStructure (op ⦋q⦌)
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro g
  apply ActionProduct.ext
  · apply Subtype.ext
    change (claim415FactorizationHom I n m q ⟨g, 1⟩).base.val = firstBlockMatrix n m g.val
    rw [claim415FactorizationHom_base]
    change matrixDropLast (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1))
      (Unitization ℤ (I.obj (op ⦋q⦌)))) * firstBlockMatrix n m g.val = _
    rw [matrixDropLast_one, one_mul]
  · change (claim415FactorizationHom I n m q ⟨g, 1⟩).fiber = 1
    rw [claim415FactorizationHom_fiber, triangularBlockGroupLastColumn_one]
    rfl

/-- 概要：Claim 4.15 の実因子化を基底変更を許す半直積対の射にする。
方針：基底にブロック安定化、全空間に実因子化を使う。
規約：KST Claim 4.15。使われ方：相対ホモロジーの実比較射。 -/
def claim415PairMap (I : NonUnitalSimplicialRing.{u}) (n m : ℕ) :
    SimplicialActionPairMap (I.triangularGLAction n (m + 1)) (I.hatGLColumnAction (n + m)) where
  base := I.hatGLBlockMap n m
  total := claim415FactorizationMap I n m
  section_comm := claim415FactorizationMap_section I n m

/-- 概要：右乗法の三角群への実射の後に因子化を行う相対写像は低次で零。
方針：実 ĜL の群状性と Lemma A.4 による零化を、相対対射の合成則で後合成する。
規約：KST Claim 4.15 の実因子化による零化。H_* の模型だけを明示的に借りる。
使われ方：通常の列のブロック安定化による写像と成分で同定する。 -/
theorem claim415_factorized_relative_zero (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (hi : i ≤ m) :
    relativeBarPairMap F
      (((I.standardIdeal.rightColumnActionHom (I.standardElement a) n m).restrict
        (I.hatGLRepresentation n)).toPairMap.comp (claim415PairMap I n m)) = 0 := by
  rw [relativeBarPairMap_comp, relativeBarPairMap_toPairMap,
    nonUnitalLemma416_relative_zero I a n m F hF M hi]
  simp

end SerrePositivity.KST.ProExcision
