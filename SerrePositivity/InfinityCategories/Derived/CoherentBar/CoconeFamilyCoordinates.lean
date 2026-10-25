module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinCoordinates
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingSpace
/-!
概要：終点固定の高次余錐族から、元の単体とパラメーターを併せた HA 単体を読む。
方針：既存の coslice fiber の射を二つの標準単体の join へ制限する。
規約：任意のパラメーター次数を扱い、正規化加群の型を変えない。
使われ方：高次の混合成分を正規化実 bar の全 Hom へ戻す。
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

def dgCoherentBarCoconeFamilySimplex {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    DGNerve.Simplex R (RightModule R D) (n + m + 1) :=
  (SSet.yonedaEquiv (X := dgNerve R (RightModule R D)))
    ((joinStdSimplexIso n m).inv ≫
      joinMap ((SSet.yonedaEquiv
        (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
        (𝟙 Δ[m]) ≫ c.val.val)

lemma dgCoherentBarCoconeFamilySimplex_left {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeFamilySimplex R D F y c s).pullback (dgCoherentBarJoinLeft n m) =
      coherentDiagramSimplex F s := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinLeft n m)) ≫
      (joinStdSimplexIso.{max (u + 1) v} n m).inv = joinInl Δ[n] Δ[m] := by
    rw [← dgCoherentBarJoinLeft_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (dgNerve R (RightModule R D)).map
    (SimplexCategory.mkHom (dgCoherentBarJoinLeft n m)).op
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInl_joinMap, Category.assoc, c.val.property,
    SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

lemma dgCoherentBarCoconeFamilySimplex_right {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeFamilySimplex R D F y c s).pullback (dgCoherentBarJoinRight n m) =
      InfinityCategories.PinchedHom.constant y m := by
  have hi : SSet.stdSimplex.map (SimplexCategory.mkHom (dgCoherentBarJoinRight n m)) ≫
      (joinStdSimplexIso.{max (u + 1) v} n m).inv = joinInr Δ[n] Δ[m] := by
    rw [← dgCoherentBarJoinRight_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (dgNerve R (RightModule R D)).map
    (SimplexCategory.mkHom (dgCoherentBarJoinRight n m)).op
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInr_joinMap, Category.id_comp]
  exact c.property

lemma dgCoherentBarCoconeFamilySimplex_source {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeFamilySimplex R D F y c s).obj 0 =
      dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) n => t.obj 0)
    (dgCoherentBarCoconeFamilySimplex_left R D F y c s)
  exact h.trans (coherentDiagramSimplex_obj F s 0)

lemma dgCoherentBarCoconeFamilySimplex_target {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    (dgCoherentBarCoconeFamilySimplex R D F y c s).obj (Fin.last (n + m + 1)) =
      dgNerve.vertexEquiv R (RightModule R D) y := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) m => t.obj (Fin.last m))
    (dgCoherentBarCoconeFamilySimplex_right R D F y c s)
  have he : dgCoherentBarJoinRight n m (Fin.last m) = Fin.last (n + m + 1) :=
    Fin.ext (by dsimp [dgCoherentBarJoinRight, joinRightOrderHom]; omega)
  change (dgCoherentBarCoconeFamilySimplex R D F y c s).obj
    (dgCoherentBarJoinRight n m (Fin.last m)) = _ at h
  rw [he] at h
  exact h

def dgCoherentBarCoconeFamilyColumn {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (dgNerve.vertexEquiv R (RightModule R D) y)).X (-(m : ℤ) - (s.1 : ℤ)) :=
  gradedHomTransport (dgCoherentBarCoconeFamilySimplex_source R D F y c s.2)
    (dgCoherentBarCoconeFamilySimplex_target R D F y c s.2) rfl
    ((dgCoherentBarCoconeFamilySimplex R D F y c s.2).hom
      Finset.univ 0 (Fin.last (s.1 + m + 1)) (-(m : ℤ) - (s.1 : ℤ))
      (coherentDiagramTop_card (s.1 + m)) (coherentDiagramTop_min (s.1 + m))
      (coherentDiagramTop_max (s.1 + m)) (by simp; omega))

end SerrePositivity.InfinityCategories
