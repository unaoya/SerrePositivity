module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseNaturality
/-!
概要：逆構成の全 HA 単体を、パラメーター図式上の slice への射へ束ねる。
方針：標準単体の join 同型と全単調写像の自然性を使う。
規約：実 dg nerve 内で束ね、模型圏の仮定を置かない。
使われ方：逆余錐族の大域的 join 射。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

abbrev dgCoherentBarInverseTargetDiagram (m : ℕ) :
    (Δ[m] : SSet.{max (u + 1) v}) ⟶ dgNerve R (RightModule R D) :=
  (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
    (InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
      (Simplex.vertex (A := R) N) m)

def dgCoherentBarInverseOverSimplex {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) : (sliceOver (dgCoherentBarInverseTargetDiagram R D N m)) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso n m).hom ≫
    (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarInverseSimplex R D F hMC N f s), ?_⟩
  rw [← Category.assoc, DGNerve.joinStdSimplexIso_inr,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
    (dgCoherentBarInverseSimplex_right R D F hMC N f s)

def dgCoherentBarInverseOverSection {p : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N p) :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶
      sliceOver (dgCoherentBarInverseTargetDiagram R D N p) where
  app n := ↾fun s => dgCoherentBarInverseOverSimplex R D F hMC N f (n := n.unop.len) s.down
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (joinStdSimplexIso m p).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarInverseSimplex R D F hMC N f (I.map α.unop.op s.down)) =
      joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[p]) ≫
        ((joinStdSimplexIso n p).hom ≫
          (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
            (dgCoherentBarInverseSimplex R D F hMC N f s.down))
    have he := dgCoherentBarInverseSimplex_map R D F hMC N f s.down
      α.unop.toOrderHom (OrderHom.id : Fin (p + 1) →o Fin (p + 1))
    rw [DGNerve.PinchedHom.LinearSimplex.pullback_id] at he
    change dgCoherentBarInverseSimplex R D F hMC N f (I.map α.unop.op s.down) =
      (dgCoherentBarInverseSimplex R D F hMC N f s.down).pullback
        (dgCoherentBarJoinOrderMap α.unop.toOrderHom
          (OrderHom.id : Fin (p + 1) →o Fin (p + 1))) at he
    rw [he]
    change (joinStdSimplexIso m p).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        ((dgNerve R (RightModule R D)).map (SimplexCategory.mkHom
          (dgCoherentBarJoinOrderMap α.unop.toOrderHom
            (OrderHom.id : Fin (p + 1) →o Fin (p + 1)))).op
          (dgCoherentBarInverseSimplex R D F hMC N f s.down)) = _
    rw [← SSet.yonedaEquiv_symm_naturality_left, ← Category.assoc]
    have hNat := dgCoherentBarJoinStdSimplex_naturality α.unop (𝟙 ⦋p⦌)
    have hId : (𝟙 ⦋p⦌) = SimplexCategory.Hom.mk
        (OrderHom.id : Fin (p + 1) →o Fin (p + 1)) := by
      ext i
      rfl
    rw [hId, SSet.stdSimplex.map_id, SimplexCategory.Hom.toOrderHom_mk] at hNat
    simpa only [Category.assoc] using congrArg (fun g => g ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarInverseSimplex R D F hMC N f s.down)) hNat.symm

lemma dgCoherentBarInverseOverSection_projection {p : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N p) :
    dgCoherentBarInverseOverSection R D F hMC N f ≫
      sliceOverProjection (dgCoherentBarInverseTargetDiagram R D N p) = F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl Δ[n] Δ[p] ≫
    ((joinStdSimplexIso n p).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarInverseSimplex R D F hMC N f s.down))) = F.app _ s
  rw [← Category.assoc, DGNerve.joinStdSimplexIso_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  exact dgCoherentBarInverseSimplex_left R D F hMC N f s.down

end SerrePositivity.InfinityCategories
