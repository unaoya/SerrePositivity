module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAhead
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoLastInsertion

/-!
模型。文献の定義との比較は後で
# 先頭と後方の二入力への合成

概要：Berger–Moerdijk §1 の先頭入力と後方の指定入力への代入を二位置の合成で表す。
方針：各部分合成の外側 arity を標準の二位置の合成へ移す。
規約：先頭位置は 0、後方の位置は 1+m、未代入の尾は k 個。
使われ方：部分合成の交換則を後半への反復合成へ拡張する。
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

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs

/-- 概要：後方へ代入してから先頭へ合成する射を標準の二位置への合成で表す（Berger–Moerdijk §1）。
方針：二つの部分合成と中間の arity の移送をテンソル代入の移送公式でまとめる。
規約：出力の arity は p+m+(k+l)。
使われ方：先頭の合成と後方の一段の挿入の交換則の右辺を正規化する。 -/
lemma composeAheadOfInputs_two (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p l : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (1 + m) k l)
      (P.composeAheadOfInputs m (k + l) p) =
    (eqToHom (congrArg P.arity (by omega : 1 + (m + 1) + k = (m + k) + 2)) ▷
      (P.arity p ⊗ P.arity l)) ≫
      P.twoSlotComposition (m + k) p l 0 ⟨1 + m, by omega⟩
        (by change 0 < 1 + m; omega) ≫
      eqToHom (congrArg P.arity (by omega : ((m + k) + p) + l = p + m + (k + l))) := by
  let e := eqToHom (congrArg P.arity (by omega : 1 + (m + 1) + k = (m + k) + 2))
  let c₁ := eqToHom (congrArg P.arity
    (by omega : ((m + k) + 1) + l = (1 + m) + (k + l)))
  let c₂ := eqToHom (congrArg P.arity
    (by omega : (1 + m) + (k + l) = ((m + k) + l) + 1))
  let c := eqToHom (congrArg P.arity
    (by omega : ((m + k) + 1) + l = ((m + k) + l) + 1))
  let o₀ := eqToHom (congrArg P.arity
    (by omega : ((m + k) + l) + p = ((m + k) + p) + l))
  let o := eqToHom (congrArg P.arity
    (by omega : ((m + k) + p) + l = p + m + (k + l)))
  let o' := eqToHom (congrArg P.arity
    (by omega : ((m + k) + l) + p = p + m + (k + l)))
  let f := P.comp ((m + k) + 1) l ⟨1 + m, by omega⟩
  let g := P.comp ((m + k) + l) p 0
  have hf : P.composeFirstInputInsertion (1 + m) k l = (e ▷ P.arity l) ≫ f ≫ c₁ :=
    P.composeFirstInputInsertion_at (1 + m) k l ((m + k) + 1) (by omega)
  have hg : P.composeAheadOfInputs m (k + l) p = (c₂ ▷ P.arity p) ≫ g ≫ o' :=
    P.composeAheadOfInputs_at m (k + l) p ((m + k) + l) (by omega)
  have hm : c₁ ≫ c₂ = c := by
    dsimp only [c₁, c₂, c]
    exact eqToHom_trans _ _
  have ho : o₀ ≫ o = o' := by
    dsimp only [o₀, o, o']
    exact eqToHom_trans _ _
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity p) ≫ g ≫ o') =
      P.twoSlotComposition (m + k) p l 0 ⟨1 + m, by omega⟩
        (by change 0 < 1 + m; omega) ≫ o := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity p) ≫ g ≫ o') =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((c ▷ P.arity p) ≫ g ≫ o₀) ≫ o
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_post]
    simp only [Category.assoc, ho]
  rw [hf, hg, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_transport, hm, hp]

/-- 概要：先頭への合成と後方の指定入力への一段の挿入は交換できる（Berger–Moerdijk §1）。
方針：両方の順序を標準の二位置への合成へ移し、その異なる入力の結合則を適用する。
規約：先頭へ p 入力、後方の指定位置へ l 入力の演算を代入する。
使われ方：先頭の部分合成と後半の有限族への反復代入を交換する帰納段階の基底となる。 -/
lemma composeAheadOfInputs_parallel (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p l : ℕ) :
    (P.composeAheadOfInputs (m + 1) k p ▷ P.arity l) ≫
      P.composeFirstInputInsertion (p + m) k l =
    (α_ (P.arity (1 + (m + 1) + k)) (P.arity p) (P.arity l)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeFirstInputInsertion (1 + m) k l)
        (P.composeAheadOfInputs m (k + l) p) := by
  let e := eqToHom (congrArg P.arity (by omega : 1 + (m + 1) + k = (m + k) + 2))
  let c₁ := eqToHom (congrArg P.arity
    (by omega : ((m + k) + 1) + p = p + (m + 1) + k))
  let c₂ := eqToHom (congrArg P.arity
    (by omega : p + m + 1 + k = ((m + k) + p) + 1))
  let c := eqToHom (congrArg P.arity
    (by omega : ((m + k) + 1) + p = ((m + k) + p) + 1))
  let o := eqToHom (congrArg P.arity
    (by omega : ((m + k) + p) + l = p + m + (k + l)))
  let f := P.comp ((m + k) + 1) p 0
  let g := P.comp ((m + k) + p) l ⟨p + m, by omega⟩
  have hf : P.composeAheadOfInputs (m + 1) k p = (e ▷ P.arity p) ≫ f ≫ c₁ :=
    P.composeAheadOfInputs_at (m + 1) k p ((m + k) + 1) (by omega)
  have hg : P.composeFirstInputInsertion (p + m) k l = (c₂ ▷ P.arity l) ≫ g ≫ o :=
    P.composeFirstInputInsertion_at (p + m) k l ((m + k) + p) (by omega)
  have hm : c₁ ≫ c₂ = c := by
    dsimp only [c₁, c₂, c]
    exact eqToHom_trans _ _
  have hpar := P.twoSlotComposition_parallel (m + k) p l (0 : Fin ((m + k) + 2))
    ⟨1 + m, by omega⟩ (by change 0 < 1 + m; omega)
  have hpos : (⟨(1 + m) + p - 1, by omega⟩ : Fin (((m + k) + p) + 1)) =
      ⟨p + m, by omega⟩ := by
    apply Fin.ext
    dsimp
    omega
  rw [hpos] at hpar
  rw [hf, hg]
  simp only [comp_whiskerRight, Category.assoc]
  conv_lhs =>
    arg 2
    arg 2
    rw [← comp_whiskerRight_assoc, hm]
  rw [P.composeAheadOfInputs_two m k p l, ← associator_naturality_left_assoc,
    reassoc_of% hpar]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
