module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoSlotComposition

/-!
模型。文献の定義との比較は後で
# 末尾二入力への代入と二位置への合成

概要：Berger–Moerdijk §1 の反復合成の二回の部分合成を、任意の二位置への合成射へ移す。
方針：二つの部分合成の外側 arity を移し、中間と終域の移送を合成する。
規約：位置 n と n+1 へ代入し、元の末尾 k 個の入力を残す。
使われ方：全入力への反復合成に二位置の外側等変性を適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local irreducible] SerrePositivity.SymmetricSequence.level
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep CategoryTheory.eqToHom

/-- 概要：末尾二入力への再帰的な代入は二位置への合成の arity の移送である（Berger–Moerdijk §1）。
方針：各部分合成を n+k を基準とする arity へ移し、テンソル代入の移送公式を使う。
規約：二位置への合成の位置は n と n+1、内側 arity は a と b。
使われ方：反復合成の二段に、二位置への合成の外側等変性を適用する。 -/
lemma composeFirstInputInsertion_two (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k a b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k b)
        (P.composeFirstInputInsertion n (k + b) a) =
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷
        (P.arity a ⊗ P.arity b)) ≫
        P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by change n < n + 1; omega) ≫
          eqToHom (congrArg P.arity (by omega : ((n + k) + a) + b = n + ((k + b) + a))) := by
  let e := eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2))
  let c₁ := eqToHom (congrArg P.arity
    (by omega : ((n + k) + 1) + b = (n + 1) + (k + b)))
  let c₂ := eqToHom (congrArg P.arity
    (by omega : (n + 1) + (k + b) = ((n + k) + b) + 1))
  let c := eqToHom (congrArg P.arity
    (by omega : ((n + k) + 1) + b = ((n + k) + b) + 1))
  let o₀ := eqToHom (congrArg P.arity
    (by omega : ((n + k) + b) + a = ((n + k) + a) + b))
  let o := eqToHom (congrArg P.arity
    (by omega : ((n + k) + a) + b = n + ((k + b) + a)))
  let o' := eqToHom (congrArg P.arity
    (by omega : ((n + k) + b) + a = n + ((k + b) + a)))
  let f := P.comp ((n + k) + 1) b ⟨n + 1, by omega⟩
  let g := P.comp ((n + k) + b) a ⟨n, by omega⟩
  have hmid : c₁ ≫ c₂ = c := by
    dsimp only [c₁, c₂, c]
    rw [eqToHom_trans]
  have hout : o₀ ≫ o = o' := by
    dsimp only [o₀, o, o']
    rw [eqToHom_trans]
  have hf : P.composeFirstInputInsertion (n + 1) k b = (e ▷ P.arity b) ≫ f ≫ c₁ := by
    exact P.composeFirstInputInsertion_at (n + 1) k b ((n + k) + 1) (by omega)
  have hg : P.composeFirstInputInsertion n (k + b) a = (c₂ ▷ P.arity a) ≫ g ≫ o' := by
    exact P.composeFirstInputInsertion_at n (k + b) a ((n + k) + b) (by omega)
  have hlast : ((c ▷ P.arity a) ≫ g ≫ o₀) ≫ o = (c ▷ P.arity a) ≫ g ≫ o' := by
    simp only [Category.assoc, hout]
  have hstandard : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity a) ≫ g ≫ o') =
      P.twoSlotComposition (n + k) a b ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by change n < n + 1; omega) ≫ o := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity a) ≫ g ≫ o') =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity a) ≫ g ≫ o₀) ≫ o
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_post, hlast]
  rw [hf, hg]
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_transport e f c₁ c₂ (g ≫ o')
  rw [ht, hmid, hstandard]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
