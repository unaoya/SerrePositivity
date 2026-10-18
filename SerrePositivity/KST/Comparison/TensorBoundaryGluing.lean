module

public import SerrePositivity.KST.Comparison.TensorSubcomplexFiniteCover
public import SerrePositivity.KST.Comparison.BoundaryVertexFaces

/-!
# 適切な面から境界全体へのホモトピー引き戻し

概要：境界の全ての適切な非空な頂点集合の面の比較から、境界全体の四角形を得る。
方針：余面の有限被覆と交叉の頂点集合の計算を、有限被覆の貼り合わせへ渡す。
規約：Segal 1974 Proposition 1.6 の有限骨格の境界の比較。
使われ方：小さい次元の行の比較から新しい行の境界の比較へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory

/--
概要：境界の適切な非空な面でのホモトピー引き戻しは、境界全体へ貼り合わさる。
方針：余面の全ての非空な交叉を一つの適切な面とし、空の交叉像は空の補題で処理する。
規約：各面の結論は明示的な局所条件であり、境界全体の結論を仮定しない。
使われ方：Segal Proposition 1.6 の有限骨格の帰納。
-/
theorem tensorBoundary_homotopyPullback_of_faces
    {X' X T' T : SSet.{u}} {n : ℕ} {f : X' ⟶ X}
    {a : X' ⊗ (SSet.boundary n : SSet.{u}) ⟶ T'} {p : T' ⟶ T}
    {b : X ⊗ (SSet.boundary n : SSet.{u}) ⟶ T}
    (sq : CommSq a (f ▷ (SSet.boundary n : SSet.{u})) p b)
    (hfaces : ∀ S : Finset (Fin (n + 1)), S.Nonempty → S ≠ Finset.univ →
      IsHomotopyPullback (tensorSubcomplexSquare (f := f) sq (boundaryVertexFace n S))) :
    IsHomotopyPullback sq := by
  classical
  apply tensorSubcomplex_homotopyPullback_of_finset_cover sq Finset.univ
    (fun i : Fin (n + 1) => boundaryVertexFace n {i}ᶜ) (boundaryVertexFace_coface_cover n)
  intro t _ ht
  rw [boundaryVertexFace_finset_inf]
  let S := t.inf (fun i => ({i}ᶜ : Finset (Fin (n + 1))))
  by_cases hS : S.Nonempty
  · exact hfaces S hS (cofaceVertexIntersection_ne_univ n t ht)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change IsHomotopyPullback (tensorSubcomplexSquare (f := f) sq (boundaryVertexFace n S))
    rw [he, boundaryVertexFace_empty]
    exact tensorSubcomplex_homotopyPullback_bot sq

end SerrePositivity.KST.Comparison
