module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardIdentityInsertionComparison
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordInsertBetweenRange
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordFactorization

/-!
# 中央恒等列の挿入と元の eraseInclusion の照合

概要：元の同じ列の像により、挿入の始域を元の削除語と同型にする。
方針：単射の列の像が共に追加列の補集合であることから、両向きの因子分解を得る。
規約：語の長さだけで同定せず、元の二つの包含との合成を厳密に回収する。
使われ方：元の削除語の graph の標準射の弱同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
open CategoryTheory ForwardPath

variable (n m : ℕ)

def toErasedData :
    {f : sourceWord n m ⟶ Word.erase (word n m) (Positions.middleColumn n m) //
      f ≫ Word.eraseInclusion (word n m) (Positions.middleColumn n m) = wordMap n m} :=
  Word.factorEmbedding _ (Word.eraseInclusion_injective _ _) (wordMap n m) (by
    change Set.range (Word.insertBetween (leftBoundaryWord n)
      (rightBoundaryWord m) .backward).orderHom ⊆ _
    rw [Word.eraseInclusion_range, Word.insertBetween_range]
    rfl)

def fromErasedData :
    {f : Word.erase (word n m) (Positions.middleColumn n m) ⟶ sourceWord n m //
      f ≫ wordMap n m = Word.eraseInclusion (word n m) (Positions.middleColumn n m)} :=
  Word.factorEmbedding (wordMap n m) (Word.insertBetween_injective _ _ _) _ (by
    change Set.range (Word.eraseInclusion (word n m) (Positions.middleColumn n m)).orderHom ⊆
      Set.range (Word.insertBetween (leftBoundaryWord n) (rightBoundaryWord m) .backward).orderHom
    rw [Word.eraseInclusion_range, Word.insertBetween_range]
    rfl)

def eraseIso : sourceWord n m ≅ Word.erase (word n m) (Positions.middleColumn n m) where
  hom := (toErasedData n m).val
  inv := (fromErasedData n m).val
  hom_inv_id := by
    apply Word.hom_ext
    intro i
    apply Word.insertBetween_injective (leftBoundaryWord n) (rightBoundaryWord m) .backward
    have h : ((toErasedData n m).val ≫ (fromErasedData n m).val) ≫ wordMap n m = wordMap n m := by
      rw [Category.assoc, (fromErasedData n m).property, (toErasedData n m).property]
    exact congrArg (fun f => f.orderHom i) h
  inv_hom_id := by
    apply Word.hom_ext
    intro i
    apply Word.eraseInclusion_injective (word n m) (Positions.middleColumn n m)
    have h : ((fromErasedData n m).val ≫ (toErasedData n m).val) ≫
        Word.eraseInclusion (word n m) (Positions.middleColumn n m) =
          Word.eraseInclusion (word n m) (Positions.middleColumn n m) := by
      rw [Category.assoc, (toErasedData n m).property, (fromErasedData n m).property]
    exact congrArg (fun f => f.orderHom i) h

lemma eraseIso_hom_fac : (eraseIso n m).hom ≫
    Word.eraseInclusion (word n m) (Positions.middleColumn n m) = wordMap n m :=
  (toErasedData n m).property

end SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
