module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
概要：次数を保つ係数環の写像と、実際の Proj の標準開の切断の引き戻しを照合する。
方針：標準開上の awayToSection の自然性を、個々の斉次分数で使う。
規約：射影スキームの射を定める irrelevant ideal の条件を指定する。
使われ方：閉厚化、基底変更、模型の遷移と共通細分の比較をつなぐ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable (G : ℕ → Submodule R S) (H : ℕ → Submodule R T) [GradedRing G] [GradedRing H]
variable (f : G →+*ᵍ H) (hf : (irrelevant H) ≤ (irrelevant G).map f)

/-- 斉次分数の係数の写像は、実際の Proj の構造層の引き戻しそのもの。
この式は閉厚化や底変換の平坦性を必要としない。 -/
theorem projectiveProjRingMapSections_apply {s : S} {d : ℕ} (hs : s ∈ G d)
    (z : Away G s) :
    ((Proj.map f hf).appLE (Proj.basicOpen G s) (Proj.basicOpen H (f s)) (by rfl)).hom
        ((Proj.awayToSection G s).hom z) =
      (Proj.awayToSection H (f s)).hom (Away.map f s z) :=
  congrArg (fun g : CommRingCat.of (Away G s) ⟶ Γ(Proj H, Proj.basicOpen H (f s)) ↦ g.hom z)
    (Proj.awayToSection_comp_appLE f hf hs)

end SerrePositivity.AlgebraicGeometry
