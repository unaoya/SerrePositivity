module

public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackLift
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：pullback の経路への鎖写像は、二射影の実経路によって一意に決まる。
方針：両端には元の pullback の一意性、比較 cochain には次数ごとの一意性を使う。
規約：両端だけでの判定はしない。使われ方：経路 lift の実代数性と普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
variable (R : Type u) [CommRing R] {A B D : Mon (Complex R)} (f : A ⟶ D) (g : B ⟶ D)
  {K : Complex R} {s t : K ⟶ (Path.algebra R (MonoidPullback.obj f g)).X}
  (hf : s ≫ Path.mapHom R (MonoidPullback.fst f g) =
    t ≫ Path.mapHom R (MonoidPullback.fst f g))
  (hg : s ≫ Path.mapHom R (MonoidPullback.snd f g) =
    t ≫ Path.mapHom R (MonoidPullback.snd f g))

include hf hg in
lemma chain_ext : s = t := by
  apply Path.chain_ext R (MonoidPullback.obj f g)
  · apply pullback.hom_ext
    · have he := congrArg (fun z => z ≫ (Path.source R A).hom) hf
      simp only [Category.assoc, Path.mapHom_source] at he
      exact he
    · have he := congrArg (fun z => z ≫ (Path.source R B).hom) hg
      simp only [Category.assoc, Path.mapHom_source] at he
      exact he
  · apply pullback.hom_ext
    · have he := congrArg (fun z => z ≫ (Path.target R A).hom) hf
      simp only [Category.assoc, Path.mapHom_target] at he
      exact he
    · have he := congrArg (fun z => z ≫ (Path.target R B).hom) hg
      simp only [Category.assoc, Path.mapHom_target] at he
      exact he
  · apply CochainPullback.hom_ext f.hom g.hom (-1)
    · change ((Cochain.ofHom s).comp (Path.primitive R (MonoidPullback.obj f g)) _).comp
        (Cochain.ofHom (MonoidPullback.fst f g).hom) _ =
          ((Cochain.ofHom t).comp (Path.primitive R (MonoidPullback.obj f g)) _).comp
            (Cochain.ofHom (MonoidPullback.fst f g).hom) _
      rw [Cochain.comp_assoc_of_first_is_zero_cochain,
        Cochain.comp_assoc_of_first_is_zero_cochain, ← Path.mapHom_primitive,
        ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hf]
      rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · change ((Cochain.ofHom s).comp (Path.primitive R (MonoidPullback.obj f g)) _).comp
        (Cochain.ofHom (MonoidPullback.snd f g).hom) _ =
          ((Cochain.ofHom t).comp (Path.primitive R (MonoidPullback.obj f g)) _).comp
            (Cochain.ofHom (MonoidPullback.snd f g).hom) _
      rw [Cochain.comp_assoc_of_first_is_zero_cochain,
        Cochain.comp_assoc_of_first_is_zero_cochain, ← Path.mapHom_primitive,
        ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hg]
      rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
