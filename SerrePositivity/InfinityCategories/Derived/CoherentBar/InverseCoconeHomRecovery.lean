module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomSpaceInverse
/-!
概要：逆余錐族から回収した全次数 Hom は、入力線形単体の全係数に一致する。
方針：全頂点の混合係数を native 成分で検出し、実 Hom の成分一意性を使う。
規約：全パラメーター次数で成り立つ。
使われ方：全写像空間比較と逆射の右逆則。
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
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeInverseSimplex_column {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) m) (s : I _⦋n⦌) :
    dgCoherentBarCoconeFamilyColumn R D F y
      (dgCoherentBarCoconeInverseSimplex R D F hMC y f) ⟨n, s⟩ =
    compose R (x := dgCoherentBarSource R D F ⟨n, s⟩)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarInverseFullHom R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y) f.val)
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + -(m : ℤ) = -(m : ℤ) - (n : ℤ) by omega) := by
  have hFamily := (dgCoherentBarCoconeFamilySimplex_full_hom_heq R D F y
    (dgCoherentBarCoconeInverseSimplex R D F hMC y f) s).symm
  rw [dgCoherentBarCoconeInverseSimplex_family] at hFamily
  have hRaw := dgCoherentBarInverseRawData_full_hom_heq R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) f.val s
  have hComp := dgCoherentBarHom_compose_degree_heq (R := R)
    (a := dgCoherentBarSource R D F ⟨n, s⟩) (b := dgCoherentBarNormalizedModule R D F hMC)
    (c := dgNerve.vertexEquiv R (RightModule R D) y)
    (p := -(n : ℤ)) (q := -(m : ℤ))
    (k := -((n + m : ℕ) : ℤ)) (l := -(m : ℤ) - (n : ℤ))
    (dgCoherentBarInverseFullHom R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y) f.val)
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) (by omega) (by omega)
  exact eq_of_heq (hFamily.trans (hRaw.trans hComp))

lemma dgCoherentBarCoconeInverseSimplex_hom {m : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) m) :
    dgCoherentBarCoconeFamilyHom R D F hMC y
      (dgCoherentBarCoconeInverseSimplex R D F hMC y f) =
      dgCoherentBarInverseFullHom R D F hMC
        (dgNerve.vertexEquiv R (RightModule R D) y) f.val := by
  apply Eq.symm
  apply dgCoherentBarCoconeFamilyHom_unique R D F hMC y
  intro s
  exact (dgCoherentBarCoconeInverseSimplex_column R D F hMC y f s.val.2).symm

end SerrePositivity.InfinityCategories
