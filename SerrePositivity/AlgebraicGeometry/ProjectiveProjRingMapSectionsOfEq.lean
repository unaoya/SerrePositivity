module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjRingMapSections

/-!
概要：写像後の分母を、指定した等しい分母で扱う標準開の自然性。
方針：指定された分母の等式を消去し、元の自然性を使う。
規約：加群の写像と比較するときに、分母の輸送を隠さない。
使われ方：実際の Proj の Čech の引き戻しと、次数零の加群の写像の照合。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]
variable (G : ℕ → Submodule R S) (H : ℕ → Submodule R A) [GradedRing G] [GradedRing H]
variable (f : G →+*ᵍ H) (hf : (irrelevant H) ≤ (irrelevant G).map f)

/-- 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 -/
theorem projectiveProjRingMapSections_of_eq {s : S} {t : A} {d : ℕ}
    (hs : s ∈ G d) (ht : t = f s)
    (hmap : Submonoid.powers s ≤ (Submonoid.powers t).comap f.toRingHom) :
    Proj.awayToSection G s ≫
      (Proj.map f hf).appLE (Proj.basicOpen G s) (Proj.basicOpen H t)
        (by rw [Proj.map_preimage_basicOpen, ht]) =
      CommRingCat.ofHom (HomogeneousLocalization.map f hmap) ≫ Proj.awayToSection H t := by
  subst t
  exact Proj.awayToSection_comp_appLE f hf hs

end SerrePositivity.AlgebraicGeometry
