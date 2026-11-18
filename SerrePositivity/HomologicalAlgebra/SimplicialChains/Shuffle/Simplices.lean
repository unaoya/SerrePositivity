module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 一般の単体集合の shuffle 単体

概要：Berger–Fresse §1.1.3 の shuffle の各項を任意の二つの単体集合で構成する。
方針：格子経路の水平・垂直の写像で単体を引き戻して積の単体を得る。
規約：正規化や係数環を用いない単体集合上の構成。
使われ方：一般の shuffle と AW の余代数適合性。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

/-- 概要：経路に沿う二つの単体の積単体（Berger–Fresse §1.1.3）。
方針：水平・垂直座標の単体圏の射によって引き戻す。
規約：p,q 次元の単体から p+q 次元の積単体を作る。
使われ方：一般の shuffle の符号付き和の一項。 -/
def simplex (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) : (X ⊗ Y) _⦋p + q⦌ :=
  ⟨X.map s.horizontalMap.op x, Y.map s.verticalMap.op y⟩

/-- 概要：shuffle の一項は単体集合の射の対に自然（Berger–Fresse §1.1.3）。
方針：二つの単体圏の射に対する自然性を使う。
規約：二つの入力の射は独立に指定できる。
使われ方：一般の shuffle の自然性。 -/
lemma simplex_natural {X X' Y Y' : SSet.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    {p q : ℕ} (s : ShufflePath p q) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (f ⊗ₘ g).app _ (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X' Y' s (f.app _ x) (g.app _ y) := by
  apply Prod.ext
  · exact congrArg (fun φ => φ x) (f.naturality s.horizontalMap.op)
  · exact congrArg (fun φ => φ y) (g.naturality s.verticalMap.op)

/-- 概要：二つの座標写像が同じ隣接頂点を潰すと積単体は退化する（Berger–Fresse §1.1.3）。
方針：両写像を同じ退化 σ_i の後の写像へ分解する。
規約：頂点だけで一般の単体の退化を判定せず、単体圏の射の分解を使う。
使われ方：退化入力から来る各 shuffle 項の退化性。 -/
lemma pairPullback_degenerate (X Y : SSet.{0}) {N k l : ℕ}
    (θ : ⦋N⦌ ⟶ ⦋k⦌) (η : ⦋N⦌ ⟶ ⦋l⦌) (i : Fin N)
    (hθ : θ.toOrderHom i.castSucc = θ.toOrderHom i.succ)
    (hη : η.toOrderHom i.castSucc = η.toOrderHom i.succ)
    (x : X _⦋k⦌) (y : Y _⦋l⦌) :
    (⟨X.map θ.op x, Y.map η.op y⟩ : (X ⊗ Y) _⦋N⦌) ∈ (X ⊗ Y).degenerate N := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N =>
    obtain ⟨θ', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective' θ i hθ
    obtain ⟨η', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective' η i hη
    have he :
        (⟨X.map (SimplexCategory.σ i ≫ θ').op x,
            Y.map (SimplexCategory.σ i ≫ η').op y⟩ : (X ⊗ Y) _⦋N + 1⦌) =
          (X ⊗ Y).σ i ⟨X.map θ'.op x, Y.map η'.op y⟩ := by
      apply Prod.ext
      · exact congrArg (fun φ => φ x) (X.map_comp θ'.op (SimplexCategory.σ i).op)
      · exact congrArg (fun φ => φ y) (Y.map_comp η'.op (SimplexCategory.σ i).op)
    rw [he]
    exact SSet.σ_mem_degenerate _ _ _

/-- 概要：第一の入力が退化写像から来ると各 shuffle 項も退化（Berger–Fresse §1.1.3）。
方針：退化位置の水平辺を持ち上げ、両座標の同じ辺の像が一致することを使う。
規約：一般の単体集合を扱い、nerve の頂点判定を仮定しない。
使われ方：shuffle を第一の入力について正規化へ降ろす。 -/
lemma simplex_σ_left (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath (p + 1) q)
    (j : Fin (p + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s (X.σ j x) y ∈ (X ⊗ Y).degenerate (p + 1 + q) := by
  obtain ⟨i, h₀, h₁, hv⟩ := s.horizontal_edge j
  have he : _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s (X.σ j x) y =
      (⟨X.map (s.horizontalMap ≫ SimplexCategory.σ j).op x,
        Y.map s.verticalMap.op y⟩ : (X ⊗ Y) _⦋p + 1 + q⦌) := by
    apply Prod.ext
    · exact congrArg (fun φ => φ x) (X.map_comp (SimplexCategory.σ j).op s.horizontalMap.op).symm
    · rfl
  rw [he]
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.pairPullback_degenerate X Y (s.horizontalMap ≫ SimplexCategory.σ j)
    s.verticalMap i _ hv x y
  change j.predAbove (s.horizontal i.castSucc) = j.predAbove (s.horizontal i.succ)
  rw [h₀, h₁, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]

/-- 概要：第二の入力が退化写像から来ると各 shuffle 項も退化（Berger–Fresse §1.1.3）。
方針：退化位置の垂直辺を持ち上げ、両座標の同じ辺の像が一致することを使う。
規約：符号の相殺を用いず各項ごとに退化を示す。
使われ方：shuffle を第二の入力について正規化へ降ろす。 -/
lemma simplex_σ_right (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p (q + 1))
    (j : Fin (q + 1)) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x (Y.σ j y) ∈ (X ⊗ Y).degenerate (p + (q + 1)) := by
  obtain ⟨i, h₀, h₁, hh⟩ := s.vertical_edge j
  have he : _root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x (Y.σ j y) =
      (⟨X.map s.horizontalMap.op x,
        Y.map (s.verticalMap ≫ SimplexCategory.σ j).op y⟩ : (X ⊗ Y) _⦋p + (q + 1)⦌) := by
    apply Prod.ext
    · rfl
    · exact congrArg (fun φ => φ y) (Y.map_comp (SimplexCategory.σ j).op s.verticalMap.op).symm
  rw [he]
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.pairPullback_degenerate X Y s.horizontalMap
    (s.verticalMap ≫ SimplexCategory.σ j) i hh _ x y
  change j.predAbove (s.vertical i.castSucc) = j.predAbove (s.vertical i.succ)
  rw [h₀, h₁, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]

end SerrePositivity.SimplicialChains.Shuffle
