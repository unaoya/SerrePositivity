module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPointedSimplex
public import SerrePositivity.InfinityCategories.Core.UniverseBoundaryHom
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
/-!
概要：指定基点球面単体の関係と積の充填を、宇宙の間で保持する。
方針：全ての指定面と定数面を同じ標準単体同型で移す。
規約：面の添字と元の充填を変えない。
使われ方：全基点 π の宇宙比較を商と群演算へ降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

lemma dgBarCompactUliftSimplexHom_face (F : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ uliftSimplexHomEquiv.{u, v} X (n + 1) F =
      uliftSimplexHomEquiv.{u, v} X n (stdSimplex.δ i ≫ F) := by
  ext d s
  rfl

lemma dgBarCompactUliftSimplexHomDown_face
    (F : (Δ[n + 1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj X)
    (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ (uliftSimplexHomEquiv.{u, v} X (n + 1)).symm F =
      (uliftSimplexHomEquiv.{u, v} X n).symm (stdSimplex.δ i ≫ F) := by
  apply (uliftSimplexHomEquiv.{u, v} X n).injective
  rw [Equiv.apply_symm_apply, ← dgBarCompactUliftSimplexHom_face, Equiv.apply_symm_apply]

lemma dgBarCompactUliftSimplexHom_const (x : X _⦋0⦌) (n : ℕ) :
    uliftSimplexHomEquiv.{u, v} X n (SSet.const x) = SSet.const (ULift.up x) := by
  change (uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map (SSet.const x) = _
  rw [dgBarCompactUliftConst, SSet.comp_const]

lemma dgBarCompactUliftSimplexHomDown_const (x : X _⦋0⦌) (n : ℕ) :
    (uliftSimplexHomEquiv.{u, v} X n).symm (SSet.const (ULift.up x)) = SSet.const x := by
  apply (uliftSimplexHomEquiv.{u, v} X n).injective
  rw [Equiv.apply_symm_apply, dgBarCompactUliftSimplexHom_const]

def dgBarCompactPointedRelUp {f g : X.PtSimplex n x} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct f g i) :
    PtSimplex.RelStruct (dgBarCompactPointedSimplexUp.{u, v} f)
      (dgBarCompactPointedSimplexUp.{u, v} g) i where
  map := uliftSimplexHomEquiv X (n + 1) r.map
  δ_castSucc_map := by rw [dgBarCompactUliftSimplexHom_face, r.δ_castSucc_map]; rfl
  δ_succ_map := by rw [dgBarCompactUliftSimplexHom_face, r.δ_succ_map]; rfl
  δ_map_of_lt j hj := by
    rw [dgBarCompactUliftSimplexHom_face, r.δ_map_of_lt j hj, dgBarCompactUliftSimplexHom_const]
  δ_map_of_gt j hj := by
    rw [dgBarCompactUliftSimplexHom_face, r.δ_map_of_gt j hj, dgBarCompactUliftSimplexHom_const]

def dgBarCompactPointedRelDown
    {f g : ((SSet.uliftFunctor.{v, u}).obj X).PtSimplex n (ULift.up x)} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct f g i) :
    PtSimplex.RelStruct (dgBarCompactPointedSimplexDown f)
      (dgBarCompactPointedSimplexDown g) i where
  map := (uliftSimplexHomEquiv X (n + 1)).symm r.map
  δ_castSucc_map := by rw [dgBarCompactUliftSimplexHomDown_face, r.δ_castSucc_map]; rfl
  δ_succ_map := by rw [dgBarCompactUliftSimplexHomDown_face, r.δ_succ_map]; rfl
  δ_map_of_lt j hj := by
    rw [dgBarCompactUliftSimplexHomDown_face, r.δ_map_of_lt j hj,
      dgBarCompactUliftSimplexHomDown_const]
  δ_map_of_gt j hj := by
    rw [dgBarCompactUliftSimplexHomDown_face, r.δ_map_of_gt j hj,
      dgBarCompactUliftSimplexHomDown_const]

def dgBarCompactPointedMulUp {f g fg : X.PtSimplex n x} {i : Fin n}
    (r : PtSimplex.MulStruct f g fg i) :
    PtSimplex.MulStruct (dgBarCompactPointedSimplexUp.{u, v} f)
      (dgBarCompactPointedSimplexUp.{u, v} g) (dgBarCompactPointedSimplexUp.{u, v} fg) i where
  map := uliftSimplexHomEquiv X (n + 1) r.map
  δ_castSucc_castSucc_map := by
    rw [dgBarCompactUliftSimplexHom_face, r.δ_castSucc_castSucc_map]; rfl
  δ_succ_castSucc_map := by rw [dgBarCompactUliftSimplexHom_face, r.δ_succ_castSucc_map]; rfl
  δ_succ_succ_map := by rw [dgBarCompactUliftSimplexHom_face, r.δ_succ_succ_map]; rfl
  δ_map_of_lt j hj := by
    rw [dgBarCompactUliftSimplexHom_face, r.δ_map_of_lt j hj, dgBarCompactUliftSimplexHom_const]
  δ_map_of_gt j hj := by
    rw [dgBarCompactUliftSimplexHom_face, r.δ_map_of_gt j hj, dgBarCompactUliftSimplexHom_const]

end SerrePositivity.InfinityCategories
