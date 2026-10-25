module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplexNaturality
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarMaurerCartan
/-!
概要：正規化実 bar を頂点とする元の coherent 図式の native 余錐を構成する。
方針：全 HA 単体を終点固定 slice へ送り、既存の slice 普遍性で join 上へ束ねる。
規約：元の図式と正規化加群の公開型を維持し、全退化写像を含む自然性を使う。
使われ方：工程Bの全 Hom 普遍性と、元の bar への比較の正規化側の入口。
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

def dgCoherentBarNativeApex : (dgNerve R (RightModule R D)) _⦋0⦌ :=
  DGNerve.Simplex.vertex (dgCoherentBarNormalizedModule R D F hMC)

lemma dgCoherentBarNativeSimplex_apex {n : ℕ} (s : I _⦋n⦌) :
    (dgNerve R (RightModule R D)).map (PinchedHom.lastVertex n).op
      (dgCoherentBarNativeSimplex R D F hMC s) =
      dgCoherentBarNativeApex R D F hMC := by
  apply (dgNerve.vertexEquiv R (RightModule R D)).injective
  change (dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)) = _
  exact dgCoherentBarNativeSimplex_last R D F hMC s

def dgCoherentBarNativeOverSimplex {n : ℕ} (s : I _⦋n⦌) :
    (sliceOver ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC))) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeSimplex R D F hMC s), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left, dgCoherentBarNativeSimplex_apex]

def dgCoherentBarNativeOverSection :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶
    sliceOver ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) where
  app n := ↾fun s => dgCoherentBarNativeOverSimplex R D F hMC (n := n.unop.len) s.down
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeSimplex R D F hMC
        (I.map α.unop.op s.down)) =
      joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((joinStdSimplexIso n 0).hom ≫
          (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
            (dgCoherentBarNativeSimplex R D F hMC s.down))
    have he := dgCoherentBarNativeSimplex_map R D F hMC s.down α.unop.toOrderHom
    change dgCoherentBarNativeSimplex R D F hMC (I.map α.unop.op s.down) =
      (dgCoherentBarNativeSimplex R D F hMC s.down).pullback
        (PinchedHom.extendOrderHom α.unop.toOrderHom) at he
    rw [he]
    change (joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      ((dgNerve R (RightModule R D)).map (PinchedHom.extend α.unop).op
        (dgCoherentBarNativeSimplex R D F hMC s.down)) = _
    rw [← SSet.yonedaEquiv_symm_naturality_left, ← Category.assoc]
    exact congrArg (fun f => f ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
            (dgCoherentBarNativeSimplex R D F hMC s.down))
      (joinStdSimplexIso_rightPoint_naturality α.unop).symm

lemma dgCoherentBarNativeOverSection_projection :
    dgCoherentBarNativeOverSection R D F hMC ≫ sliceOverProjection
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeApex R D F hMC)) = F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl Δ[n] Δ[0] ≫
    ((joinStdSimplexIso n 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
            (dgCoherentBarNativeSimplex R D F hMC s.down))) = F.app _ s
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  change (dgCoherentBarNativeSimplex R D F hMC s.down).pullback
    Fin.castSuccOrderEmb.toOrderHom = coherentDiagramSimplex F s.down
  exact dgCoherentBarNativeSimplex_front R D F hMC s.down

def dgCoherentBarNormalizedNativeCocone : JoinCocone F :=
  ⟨sliceOverUncurry (dgCoherentBarNativeOverSection R D F hMC), by
    rw [sliceOverUncurry_projection, dgCoherentBarNativeOverSection_projection]⟩

lemma dgCoherentBarNormalizedNativeCocone_vertex :
    (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex =
      dgCoherentBarNativeApex R D F hMC := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv
    (joinInr _ Δ[0] ≫ sliceOverUncurry (dgCoherentBarNativeOverSection R D F hMC)) = _
  rw [sliceOverUncurry_fixed, Equiv.apply_symm_apply]

abbrev dgCoherentBarNormalizedNativeCoconeUnconditional : JoinCocone F :=
  dgCoherentBarNormalizedNativeCocone R D F (dgCoherentBarTheta_maurerCartan R D F)

end SerrePositivity.InfinityCategories
