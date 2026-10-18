module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# 境界の頂点集合による面の有限被覆

概要：標準単体の各面を境界の部分単体集合へ引き戻し、交叉と面の有限被覆を計算する。
方針：頂点集合の面の交叉と、境界の余面による和を使う。
規約：Segal 1974 Proposition 1.6 の境界の有限交叉の比較。
使われ方：各適切な面の四角形から境界全体へ貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open scoped Simplicial

/--
概要：頂点集合の面を標準単体の境界の部分対象として読む。
方針：標準単体の面を境界の包含に沿って引き戻す。
規約：頂点集合が全体なら境界全体、空なら空部分対象になる。
使われ方：境界の有限被覆の各片と交叉。
-/
def boundaryVertexFace (n : ℕ) (S : Finset (Fin (n + 1))) :
    (SSet.boundary.{u} n : SSet.{u}).Subcomplex :=
  (SSet.stdSimplex.face S).preimage (SSet.boundary n).ι

/--
概要：境界の頂点集合による面の交叉は、頂点集合の交叉の面である。
方針：標準単体の面の交叉を引き戻す。
規約：交叉が空でも成立する。
使われ方：有限被覆の全ての交叉の同定。
-/
theorem boundaryVertexFace_inf (n : ℕ) (S T : Finset (Fin (n + 1))) :
    boundaryVertexFace.{u} n S ⊓ boundaryVertexFace n T = boundaryVertexFace n (S ⊓ T) := by
  unfold boundaryVertexFace
  rw [← SSet.stdSimplex.face_inter_face]
  rfl

/--
概要：全ての頂点を指定した境界の面は境界全体である。
方針：標準単体の全頂点の面を引き戻す。
規約：右辺は境界の部分対象の束の最大元。
使われ方：空の交叉の計算。
-/
theorem boundaryVertexFace_univ (n : ℕ) : boundaryVertexFace.{u} n Finset.univ = ⊤ := by
  unfold boundaryVertexFace
  rw [SSet.stdSimplex.face_univ]
  rfl

/--
概要：頂点集合が空の境界の面は空である。
方針：標準単体の空の面を引き戻す。
規約：空対象の四角形にそのまま適用する。
使われ方：面の交叉が空の場合。
-/
theorem boundaryVertexFace_empty (n : ℕ) : boundaryVertexFace.{u} n ∅ = ⊥ := by
  unfold boundaryVertexFace
  rw [SSet.stdSimplex.face_empty]
  rfl

/--
概要：境界の面の有限交叉は、頂点集合の有限交叉の面である。
方針：二項の交叉と全体の面の計算から有限帰納する。
規約：空の添字集合も含める。
使われ方：有限部分族の交叉を一つの面として扱う。
-/
theorem boundaryVertexFace_finset_inf (n : ℕ) {ι : Type*} (s : Finset ι)
    (S : ι → Finset (Fin (n + 1))) :
    s.inf (fun i => boundaryVertexFace.{u} n (S i)) = boundaryVertexFace n (s.inf S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact (boundaryVertexFace_univ n).symm
  | @insert i s hi ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ih, boundaryVertexFace_inf]

/--
概要：一つの頂点を除いた面の有限和は境界全体である。
方針：境界の標準単体の余面による和を各次数で引き戻す。
規約：全ての頂点を添字に取る有限被覆。
使われ方：有限被覆の和から境界全体の四角形へ戻す。
-/
theorem boundaryVertexFace_coface_cover (n : ℕ) :
    Finset.univ.sup (fun i : Fin (n + 1) => boundaryVertexFace.{u} n {i}ᶜ) = ⊤ := by
  apply le_antisymm le_top
  intro d s _
  let x : Δ[n].obj d := s.1
  have hs : x ∈ (SSet.boundary n).obj d := s.2
  rw [SSet.boundary_eq_iSup, Subfunctor.iSup_obj] at hs
  simp only [Set.mem_iUnion] at hs
  obtain ⟨i, hi⟩ := hs
  simp only [Finset.sup_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨i, Finset.mem_univ i, hi⟩

/--
概要：余面の非空な部分族の頂点集合の交叉は、全頂点集合とは異なる。
方針：部分族から一つの除かれる頂点を選ぶ。
規約：交叉そのものが空である場合も含める。
使われ方：有限被覆の全ての非空な交叉が適切な面であること。
-/
theorem cofaceVertexIntersection_ne_univ (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    s.inf (fun i => ({i}ᶜ : Finset (Fin (n + 1)))) ≠ Finset.univ := by
  obtain ⟨i, hi⟩ := hs
  intro h
  have hle : s.inf (fun j => ({j}ᶜ : Finset (Fin (n + 1)))) ≤ {i}ᶜ := Finset.inf_le hi
  rw [h] at hle
  have hh := hle (Finset.mem_univ i)
  simp at hh

end SerrePositivity.KST.Comparison
