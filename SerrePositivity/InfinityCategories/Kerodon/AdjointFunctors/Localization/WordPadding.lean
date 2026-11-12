module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendImages
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection

/-!
# 両端の元の語を固定して列を追加する関手

概要：固定した左右の語の間に元の語を置き、全列の向きと全写像を保持する。
方針：元の連結写像を二回使い、中央の列番号の包含を自然変換へ束ねる。
規約：空語も含む。backward 一列ずつの追加を padding と呼ぶ。
使われ方：三本矢への分数計算と元の余極限の比較図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def sandwichFunctor (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a q)
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 q))
  map_id a := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_id, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_id]
  map_comp f g := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_comp, Category.id_comp]
    congr 1
    simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_comp f (𝟙 q) g (𝟙 q)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichFunctor)


def sandwichInclusion (p q a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : a ⟶ (sandwichFunctor p q).obj a where
  orderHom :=
    { toFun i := (i.castAdd q.length).natAdd p.length
      monotone' _ _ h := Nat.add_le_add_left h _ }
  direction_eq i := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a q) (i.castAdd q.length)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a q i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichInclusion)


lemma sandwichInclusion_injective (p q a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    Function.Injective (sandwichInclusion p q a).orderHom := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  change p.length + i.val = p.length + j.val at he
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichInclusion_injective)


def sandwichInclusionNat (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : 𝟭 _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⟶ sandwichFunctor p q where
  app := sandwichInclusion p q
  naturality a b f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
    intro i
    change (sandwichInclusion p q b).orderHom (f.orderHom i) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 q))).orderHom
        ((i.castAdd q.length).natAdd p.length)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap_left]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichInclusionNat)


lemma sandwichMap_injective (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) :
    Function.Injective ((sandwichFunctor p q).map f).orderHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_injective _ _ Function.injective_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_injective _ _ hf Function.injective_id)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichMap_injective)


abbrev paddingFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := sandwichFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingFunctor)


abbrev paddingInclusionNat : 𝟭 _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⟶ paddingFunctor :=
  sandwichInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddingInclusionNat)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
