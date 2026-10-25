module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterLeftCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeParameterRightCut
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComposite
/-!
概要：パラメーター側の HA 切断合成は最後以外で零、最後では最終面の高次 Hom となる。
方針：定値側の右因子を零または単位へ同定し、全次数の合成則を適用する。
規約：実際の切断点の対象と次数の輸送を明示する。
使われ方：パラメーター側の有限和を標準面の境界式へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilySimplex_parameter_obj {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) (a : Fin (m + 1)) :
    (dgCoherentBarCoconeFamilySimplex R D F y c s).obj (dgCoherentBarJoinRight n m a) =
      dgNerve.vertexEquiv R (RightModule R D) y :=
  congrArg (fun t : DGNerve.Simplex R (RightModule R D) m => t.obj a)
    (dgCoherentBarCoconeFamilySimplex_right R D F y c s)

lemma dgCoherentBarCoconeFamilyFullComposite_parameter_zero {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    dgCoherentBarFullComposite
      (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n) = 0 := by
  let T := (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  have hpos : dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hy : T.obj (j.natAdd n).succ.castSucc = dgNerve.vertexEquiv R (RightModule R D) y := by
    rw [← hpos]
    exact dgCoherentBarCoconeFamilySimplex_parameter_obj R D F y c s j.castSucc
  have hz := dgCoherentBarCoconeFamilySimplex_target R D F y c s
  have hq : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      ((j.natAdd n).succ.castSucc ≤ ·)).card : ℤ)) =
      2 - ((dgCoherentBarParameterTail j).card : ℤ) := by
    rw [dgCoherentBarFullRight_card, dgCoherentBarParameterTail_card]
    simp only [Fin.val_natAdd]
    have := j.isLt
    omega
  have hZero := gradedHom_zero_heq (A := R) (D := RightModule R D) hy hz hq
  have hRight : dgCoherentBarFullRight T (j.natAdd n) = 0 :=
    eq_of_heq ((dgCoherentBarCoconeFamilyFullRight_parameter_zero R D F y c s j hj).trans
      hZero.symm)
  change compose R (dgCoherentBarFullRight T (j.natAdd n))
    (dgCoherentBarFullLeft T (j.natAdd n)) _ = 0
  rw [hRight, DGNerve.zero_compose]

lemma dgCoherentBarCoconeFamilyFullComposite_parameter_last
    (hMC : dgCoherentBarMaurerCartan R D F) {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) :
    HEq (dgCoherentBarFullComposite
      (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData ((Fin.last m).natAdd n))
      (compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgNerve.vertexEquiv R (RightModule R D) y)
        (dgCoherentBarCoconeFamilyHom R D F hMC y
          ((coconeMappingSpace F y).δ (Fin.last (m + 1)) c))
        (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
        (show -(n : ℤ) + -(m : ℤ) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega)) := by
  let T := (dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  let j := (Fin.last m).natAdd n
  have hpos : dgCoherentBarJoinRight n (m + 1) (Fin.last m).castSucc = j.succ.castSucc :=
    Fin.ext (by change n + 1 + m = n + m + 1; omega)
  have hy : T.obj j.succ.castSucc = dgNerve.vertexEquiv R (RightModule R D) y := by
    rw [← hpos]
    exact dgCoherentBarCoconeFamilySimplex_parameter_obj R D F y c s (Fin.last m).castSucc
  have hz := dgCoherentBarCoconeFamilySimplex_target R D F y c s
  have hq : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      (j.succ.castSucc ≤ ·)).card : ℤ)) = 0 := by
    rw [dgCoherentBarFullRight_card]
    simp only [j, Fin.val_natAdd, Fin.val_last]
    omega
  have hUnit := DGNerve.unit_compose_of_heq (A := R)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarFullRight T j) (dgCoherentBarFullLeft T j)
    (by rw [dgCoherentBarFullLeft_card, dgCoherentBarFullRight_card]
        simp only [j, Fin.val_natAdd, Fin.val_last]
        omega)
    (hy.trans hz.symm) hq
    ((dgCoherentBarCoconeFamilyFullRight_parameter_unit R D F y c s).trans
      (dgCoherentBarHom_unit_heq hz.symm))
  refine hUnit.trans ((dgCoherentBarCoconeFamilyFullLeft_parameter_last R D F hMC y c s).trans ?_)
  exact dgCoherentBarHom_compose_degree_heq (R := R)
    (p := -(n : ℤ)) (q := -(m : ℤ)) (k := -(n : ℤ) + -(m : ℤ))
    (l := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (a := dgCoherentBarSource R D F ⟨n, s⟩) (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgNerve.vertexEquiv R (RightModule R D) y)
    (dgCoherentBarCoconeFamilyHom R D F hMC y
      ((coconeMappingSpace F y).δ (Fin.last (m + 1)) c))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) rfl (by omega)

end SerrePositivity.InfinityCategories
