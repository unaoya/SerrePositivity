module

public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFirstCut
public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorColumns

/-!
# 元の全縦射と最初の非指定列切断の両立

概要：元の各列の全縦射から、同じ最初の非指定生成矢と両側の正方形を回収する。
方針：元の Zigzag.Hom.comm を、一意な FirstCut の正方形の分解に代入する。
規約：元の指定縦射と元の射列の一致を保持する。
使われ方：全行を同じ非指定生成矢で切る hammock の自由積分解。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C}

lemma column_firstCut_square {S T : Zigzag W.paths w X Y} (f : S ⟶ T) (i : Fin w.length)
    (P : FirstCut W (S.arrow i)) (Q : FirstCut W (T.arrow i)) :
    (⟨P.source, P.target, P.arrow⟩ : Quiver.Total C) = ⟨Q.source, Q.target, Q.arrow⟩ ∧
      HEq P.left ((f.app (w.source i)).comp Q.left) ∧
        HEq (P.right.comp (f.app (w.target i))) Q.right :=
  first_split_square W (S.arrow i) (T.arrow i) (f.app (w.source i)) (f.app (w.target i))
    (f.app_mem (w.source i)) P.arrow Q.arrow P.left P.right Q.left Q.right
    P.left_mem Q.left_mem P.unmarked Q.unmarked P.factorization Q.factorization (f.comm i)

lemma column_firstCut_row {n : SimplexCategoryᵒᵖ} (τ : (graph W.paths w X Y).obj n)
    (k : Fin (n.unop.len + 1)) (i : Fin w.length)
    (P : FirstCut W ((τ.obj 0).arrow i)) (Q : FirstCut W ((τ.obj k).arrow i)) :
    (⟨P.source, P.target, P.arrow⟩ : Quiver.Total C) = ⟨Q.source, Q.target, Q.arrow⟩ ∧
      HEq P.left (((τ.map (homOfLE (Fin.zero_le k))).app (w.source i)).comp Q.left) ∧
        HEq (P.right.comp ((τ.map (homOfLE (Fin.zero_le k))).app (w.target i))) Q.right :=
  column_firstCut_square W (τ.map (homOfLE (Fin.zero_le k))) i P Q

def columnFirstCut (S : Zigzag W.paths w X Y) (i : Fin w.length)
    (h : column W S i ≠ []) : FirstCut W (S.arrow i) := firstCut W (S.arrow i) h

def rowFirstCut {n : SimplexCategoryᵒᵖ} (τ : (graph W.paths w X Y).obj n)
    (i : Fin w.length) (h : column W (τ.obj 0) i ≠ []) (k : Fin (n.unop.len + 1)) :
    FirstCut W ((τ.obj k).arrow i) :=
  columnFirstCut W (τ.obj k) i (by rw [column_row W τ k i]; exact h)

lemma column_firstCut_forward (S : Zigzag W.paths w X Y) (i : Fin w.length)
    (P : FirstCut W (S.arrow i)) : w.direction i = .forward := by
  cases hi : w.direction i with
  | forward => rfl
  | backward =>
    exact ((firstCut_nonempty_iff W (S.arrow i)).1 ⟨P⟩ (S.backward_mem i hi)).elim

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
