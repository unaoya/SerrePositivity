module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddedErasureRange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordFactorization

/-!
# padding 後の削除語と全体の削除語の比較同型

概要：元の列の像が等しい二つの包含の間に、元の挿入と可換な同型を構成する。
方針：元の単射への両向きの因子分解と単射性を使う。
規約：長さだけでは同定せず、元の写像への一致を証明する。
使われ方：padded な語の eraseInclusion の弱同値性を padding.map へ戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)

def toErasedData :
    {f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) //
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap_range])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.PaddedErasure.toErasedData export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (toErasedData)


def fromErasedData :
    {f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w p) //
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p)} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap_injective w p) _ (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap_range])

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.PaddedErasure.fromErasedData export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (fromErasedData)


def eraseIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w p) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) where
  hom := (toErasedData w p).val
  inv := (fromErasedData w p).val
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap_injective w p
    have h : ((toErasedData w p).val ≫ (fromErasedData w p).val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p =
        paddedEraseMap w p := by
      rw [Category.assoc, (fromErasedData w p).property, (toErasedData w p).property]
    exact congrArg (fun f => f.orderHom i) h
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p)
    have h : ((fromErasedData w p).val ≫ (toErasedData w p).val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) := by
      rw [Category.assoc, (toErasedData w p).property, (fromErasedData w p).property]
    exact congrArg (fun f => f.orderHom i) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.PaddedErasure.eraseIso export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (eraseIso)


lemma eraseIso_hom_fac : (eraseIso w p).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedEraseMap w p :=
  (toErasedData w p).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.PaddedErasure.eraseIso_hom_fac export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (eraseIso_hom_fac)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
