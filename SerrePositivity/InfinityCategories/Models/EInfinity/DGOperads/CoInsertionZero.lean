module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
模型。文献の定義との比較は後で
# 先頭出力への余演算の代入

概要：Berger–Fresse §3.1 の先頭への余演算の代入を前半ブロックの展開で記述する。
方針：空の前方ブロックとの交換を単位子で相殺する。
規約：余演算の出力数は零でもよく、後半ブロックは固定する。
使われ方：convolution の先頭位置の部分合成則を二ブロック評価へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：先頭の余代入は先頭因子の展開と後半ブロックの連結である（BF §3.1）。
方針：零重の前方ブロックの分割と係数の交換を単位子で消す。
規約：出力の arity は n+m から m+n へ移送する。
使われ方：部分合成の余演算の先頭の計算を反復評価の連結公式へ接続する。 -/
lemma tensorCoInsertionAction_zero (X C : Complex A) (m n : ℕ)
    (θ : C ⊗ X ⟶ power X n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction X C m n 0 θ =
      (α_ C X (power X m)).inv ≫ (θ ▷ power X m) ≫ (appendIso X n m).hom ≫
        eqToHom (congrArg (power X) (Nat.add_comm n m)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction
  dsimp only [Fin.val_zero, Nat.sub_zero]
  simp only [appendIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [← whiskerLeft_comp_assoc (𝟙_ (Complex A)),
    ← whiskerLeft_comp_assoc (𝟙_ (Complex A))]
  simp only [Category.assoc]
  erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertion_unitPrefix (C := C) (T := X ⊗ power X m)
    (Y := power X (n + m))
    ((α_ C X (power X m)).inv ≫ (θ ▷ power X m) ≫ (appendIso X n m).hom))]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
