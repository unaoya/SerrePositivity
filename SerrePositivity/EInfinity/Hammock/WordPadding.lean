module

public import SerrePositivity.EInfinity.Hammock.WordAppendImages
public import SerrePositivity.EInfinity.Hammock.WordIntersection

/-!
# 両端の元の語を固定して列を追加する関手

概要：固定した左右の語の間に元の語を置き、全列の向きと全写像を保持する。
方針：元の連結写像を二回使い、中央の列番号の包含を自然変換へ束ねる。
規約：空語も含む。backward 一列ずつの追加を padding と呼ぶ。
使われ方：三本矢への分数計算と元の余極限の比較図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

def sandwichFunctor (p q : Word) : Word ⥤ Word where
  obj a := append p (append a q)
  map f := appendMap (𝟙 p) (appendMap f (𝟙 q))
  map_id a := by rw [appendMap_id, appendMap_id]
  map_comp f g := by
    rw [← appendMap_comp, Category.id_comp]
    congr 1
    simpa only [Category.id_comp] using appendMap_comp f (𝟙 q) g (𝟙 q)

def sandwichInclusion (p q a : Word) : a ⟶ (sandwichFunctor p q).obj a where
  orderHom :=
    { toFun i := (i.castAdd q.length).natAdd p.length
      monotone' _ _ h := Nat.add_le_add_left h _ }
  direction_eq i := by
    exact (append_direction_right p (append a q) (i.castAdd q.length)).trans
      (append_direction_left a q i)

lemma sandwichInclusion_injective (p q a : Word) :
    Function.Injective (sandwichInclusion p q a).orderHom := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  change p.length + i.val = p.length + j.val at he
  omega

def sandwichInclusionNat (p q : Word) : 𝟭 Word ⟶ sandwichFunctor p q where
  app := sandwichInclusion p q
  naturality a b f := by
    apply hom_ext
    intro i
    change (sandwichInclusion p q b).orderHom (f.orderHom i) =
      (appendMap (𝟙 p) (appendMap f (𝟙 q))).orderHom
        ((i.castAdd q.length).natAdd p.length)
    rw [appendMap_right, appendMap_left]
    rfl

lemma sandwichMap_injective (p q : Word) {a b : Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) :
    Function.Injective ((sandwichFunctor p q).map f).orderHom :=
  appendMap_injective _ _ Function.injective_id (appendMap_injective _ _ hf Function.injective_id)

abbrev paddingFunctor : Word ⥤ Word := sandwichFunctor (single .backward) (single .backward)

abbrev paddingInclusionNat : 𝟭 Word ⟶ paddingFunctor :=
  sandwichInclusionNat (single .backward) (single .backward)

end SerrePositivity.EInfinity.Hammock.Word
