module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyNaturality
/-!
概要：標準 Hom の持ち上げを調べるため、終点が動く余錐族の HA 座標を読む。
方針：coslice の実単体を二つの標準単体の join に制限する。
規約：終点を定値と仮定せず、純粋な右面をそのまま保持する。
使われ方：固定終点経路での持ち上げの高次成分と、その境界の比較。
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

def dgCoherentBarCoconeLiftSimplex {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    DGNerve.Simplex R (RightModule R D) (n + m + 1) :=
  (SSet.yonedaEquiv (X := dgNerve R (RightModule R D)))
    ((joinStdSimplexIso n m).inv ≫
      joinMap ((SSet.yonedaEquiv
        (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
        (𝟙 Δ[m]) ≫ c.val)

lemma dgCoherentBarCoconeLiftSimplex_fixed {m n : ℕ}
    (y : (dgNerve R (RightModule R D)) _⦋0⦌)
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    dgCoherentBarCoconeLiftSimplex R D F c.val s =
      dgCoherentBarCoconeFamilySimplex R D F y c s := rfl

lemma dgCoherentBarCoconeLiftSimplex_left {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeLiftSimplex R D F c s).pullback (dgCoherentBarJoinLeft n m) =
      coherentDiagramSimplex F s := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinLeft n m)) ≫
      (joinStdSimplexIso.{max (u + 1) v} n m).inv = joinInl Δ[n] Δ[m] := by
    rw [← dgCoherentBarJoinLeft_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (dgNerve R (RightModule R D)).map
    (SimplexCategory.mkHom (dgCoherentBarJoinLeft n m)).op
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInl_joinMap, Category.assoc, c.property,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

lemma dgCoherentBarCoconeLiftSimplex_right {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeLiftSimplex R D F c s).pullback (dgCoherentBarJoinRight n m) =
      (sliceUnderProjection F).app (Opposite.op ⦋m⦌) c := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinRight n m)) ≫
      (joinStdSimplexIso.{max (u + 1) v} n m).inv = joinInr Δ[n] Δ[m] := by
    rw [← dgCoherentBarJoinRight_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (dgNerve R (RightModule R D)).map
    (SimplexCategory.mkHom (dgCoherentBarJoinRight n m)).op
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInr_joinMap, Category.id_comp]
  rfl

lemma dgCoherentBarCoconeLiftSimplex_source {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeLiftSimplex R D F c s).obj 0 =
      dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) n => t.obj 0)
    (dgCoherentBarCoconeLiftSimplex_left R D F c s)
  exact h.trans (coherentDiagramSimplex_obj F s 0)

def dgCoherentBarCoconeLiftTarget {m : ℕ} (c : (sliceUnder F) _⦋m⦌) : RightModule R D :=
  ((sliceUnderProjection F).app (Opposite.op ⦋m⦌) c).obj (Fin.last m)

lemma dgCoherentBarCoconeLiftSimplex_target {m n : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeLiftSimplex R D F c s).obj (Fin.last (n + m + 1)) =
      dgCoherentBarCoconeLiftTarget R D F c := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) m => t.obj (Fin.last m))
    (dgCoherentBarCoconeLiftSimplex_right R D F c s)
  have he : dgCoherentBarJoinRight n m (Fin.last m) = Fin.last (n + m + 1) :=
    Fin.ext (by dsimp [dgCoherentBarJoinRight, joinRightOrderHom]; omega)
  change (dgCoherentBarCoconeLiftSimplex R D F c s).obj
    (dgCoherentBarJoinRight n m (Fin.last m)) = _ at h
  rw [he] at h
  exact h

def dgCoherentBarCoconeLiftColumn {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (dgCoherentBarCoconeLiftTarget R D F c)).X (-(m : ℤ) - (s.1 : ℤ)) :=
  gradedHomTransport (dgCoherentBarCoconeLiftSimplex_source R D F c s.2)
    (dgCoherentBarCoconeLiftSimplex_target R D F c s.2) rfl
    ((dgCoherentBarCoconeLiftSimplex R D F c s.2).hom
      Finset.univ 0 (Fin.last (s.1 + m + 1)) (-(m : ℤ) - (s.1 : ℤ))
      (coherentDiagramTop_card (s.1 + m)) (coherentDiagramTop_min (s.1 + m))
      (coherentDiagramTop_max (s.1 + m)) (by simp; omega))

end SerrePositivity.InfinityCategories
