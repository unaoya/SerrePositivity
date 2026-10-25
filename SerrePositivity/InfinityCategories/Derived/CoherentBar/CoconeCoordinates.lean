module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCocone
/-!
概要：任意の元の native 余錐から、元の単体と余錐頂点を端点に持つ係数を取り出す。
方針：標準単体との join に制限し、最後を加えた HA 単体の最上成分を使う。
規約：正規化余錐だけに限定せず、任意の JoinCocone を入力に取る。
使われ方：native Hom 普遍性の逆写像と閉列方程式の回収。
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

def dgCoherentBarCoconeModule (c : JoinCocone F) : RightModule R D :=
  dgNerve.vertexEquiv R (RightModule R D) c.vertex

def dgCoherentBarCoconeSimplex (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    DGNerve.Simplex R (RightModule R D) (n + 1) :=
  (SSet.yonedaEquiv (X := dgNerve R (RightModule R D)))
    ((joinStdSimplexIso n 0).inv ≫
      joinMap ((SSet.yonedaEquiv
        (X := (SSet.uliftFunctor.{max (u + 1) v, u}).obj I)).symm (ULift.up s))
        (𝟙 Δ[0]) ≫ c.val)

lemma dgCoherentBarCoconeSimplex_front (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarCoconeSimplex R D F c s).pullback Fin.castSuccOrderEmb.toOrderHom =
      coherentDiagramSimplex F s := by
  have hi : SSet.stdSimplex.map (PinchedHom.front n) ≫ (joinStdSimplexIso n 0).inv =
      joinInl Δ[n] Δ[0] := by
    apply (cancel_mono (joinStdSimplexIso n 0).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      joinStdSimplexIso_rightPoint_inl]
  change (dgNerve R (RightModule R D)).map (PinchedHom.front n).op
    ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInl_joinMap, Category.assoc, c.property]
  rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
  rfl

lemma dgCoherentBarCoconeSimplex_last (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarCoconeSimplex R D F c s).obj (Fin.last (n + 1)) =
      dgCoherentBarCoconeModule R D F c := by
  have hi : SSet.stdSimplex.map (PinchedHom.lastVertex n) ≫ (joinStdSimplexIso n 0).inv =
      joinInr Δ[n] Δ[0] := by
    apply (cancel_mono (joinStdSimplexIso n 0).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      joinStdSimplexIso_rightPoint_inr]
  change (dgNerve.vertexEquiv R (RightModule R D))
    ((dgNerve R (RightModule R D)).map (PinchedHom.lastVertex n).op
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))) _)) = _
  rw [SSet.yonedaEquiv_naturality, ← Category.assoc, ← Category.assoc, hi,
    joinInr_joinMap, Category.id_comp]
  rfl

lemma dgCoherentBarCoconeSimplex_source (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarCoconeSimplex R D F c s).obj 0 = dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) n => t.obj 0)
    (dgCoherentBarCoconeSimplex_front R D F c s)
  exact h.trans (coherentDiagramSimplex_obj F s 0)

def dgCoherentBarCoconeColumn (c : JoinCocone F) (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (dgCoherentBarCoconeModule R D F c)).X (-(s.1 : ℤ)) :=
  gradedHomTransport (dgCoherentBarCoconeSimplex_source R D F c s.2)
    (dgCoherentBarCoconeSimplex_last R D F c s.2) rfl
    ((dgCoherentBarCoconeSimplex R D F c s.2).hom Finset.univ 0 (Fin.last (s.1 + 1))
      (-(s.1 : ℤ)) (coherentDiagramTop_card s.1) (coherentDiagramTop_min s.1)
      (coherentDiagramTop_max s.1) (by simp; omega))

end SerrePositivity.InfinityCategories
