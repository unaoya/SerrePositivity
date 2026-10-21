module

public import SerrePositivity.EInfinity.Hammock.WordPaddedErasureRange
public import SerrePositivity.EInfinity.Hammock.WordFactorization

/-!
# padding 後の削除語と全体の削除語の比較同型

概要：元の列の像が等しい二つの包含の間に、元の挿入と可換な同型を構成する。
方針：元の単射への両向きの因子分解と単射性を使う。
規約：長さだけでは同定せず、元の写像への一致を証明する。
使われ方：padded な語の eraseInclusion の弱同値性を padding.map へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.PaddedErasure
open CategoryTheory

variable (w : Word) (p : Fin w.length)

def toErasedData :
    {f : paddingFunctor.obj (erase w p) ⟶ erase (paddingFunctor.obj w) (paddedColumn w p) //
      f ≫ eraseInclusion (paddingFunctor.obj w) (paddedColumn w p) = paddedEraseMap w p} :=
  Word.factorEmbedding _ (eraseInclusion_injective _ _) (paddedEraseMap w p) (by
    rw [eraseInclusion_range, paddedEraseMap_range])

def fromErasedData :
    {f : erase (paddingFunctor.obj w) (paddedColumn w p) ⟶ paddingFunctor.obj (erase w p) //
      f ≫ paddedEraseMap w p = eraseInclusion (paddingFunctor.obj w) (paddedColumn w p)} :=
  Word.factorEmbedding (paddedEraseMap w p) (paddedEraseMap_injective w p) _ (by
    rw [eraseInclusion_range, paddedEraseMap_range])

def eraseIso : paddingFunctor.obj (erase w p) ≅
    erase (paddingFunctor.obj w) (paddedColumn w p) where
  hom := (toErasedData w p).val
  inv := (fromErasedData w p).val
  hom_inv_id := by
    apply Word.hom_ext
    intro i
    apply paddedEraseMap_injective w p
    have h : ((toErasedData w p).val ≫ (fromErasedData w p).val) ≫ paddedEraseMap w p =
        paddedEraseMap w p := by
      rw [Category.assoc, (fromErasedData w p).property, (toErasedData w p).property]
    exact congrArg (fun f => f.orderHom i) h
  inv_hom_id := by
    apply Word.hom_ext
    intro i
    apply eraseInclusion_injective (paddingFunctor.obj w) (paddedColumn w p)
    have h : ((fromErasedData w p).val ≫ (toErasedData w p).val) ≫
        eraseInclusion (paddingFunctor.obj w) (paddedColumn w p) =
          eraseInclusion (paddingFunctor.obj w) (paddedColumn w p) := by
      rw [Category.assoc, (toErasedData w p).property, (fromErasedData w p).property]
    exact congrArg (fun f => f.orderHom i) h

lemma eraseIso_hom_fac : (eraseIso w p).hom ≫
    eraseInclusion (paddingFunctor.obj w) (paddedColumn w p) = paddedEraseMap w p :=
  (toErasedData w p).property

end SerrePositivity.EInfinity.Hammock.Word.PaddedErasure
