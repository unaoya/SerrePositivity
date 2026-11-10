module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic

/-!
概要：縮小する区間の共通部分と filtered 余極限（BM18 Definition 4.6）。
方針：下端で零になる元と、上端の外で可逆になる元をそれぞれ有限段で検出する。
規約：区間の共通部分は端点ごとの元の条件で指定する。
使われ方：一点に縮む区間族から剰余体を得る。
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors

namespace SerrePositivity

variable {V : Type u} [CommRing V] {J : Type v} [Preorder J]
variable (lo hi : J → PrimeSpectrum V)
variable (hlo : Monotone lo) (hhi : Antitone hi) (h : ∀ j, lo j ≤ hi j)

/-- 縮小する区間族に対応する可換環の図式（BM18 Definition 4.6）。 -/
def intervalRingDiagram : J ⥤ CommRingCat.{u} where
  obj j := CommRingCat.of (ValuationIntervalRing (h j))
  map f := CommRingCat.ofHom (intervalRingMap (h _) (h _) (hlo f.le) (hhi f.le))
  map_id j := by
    apply CommRingCat.hom_ext
    apply intervalRing_hom_ext (h j)
    intro x
    exact intervalRingMap_algebraMap (h j) (h j) le_rfl le_rfl x
  map_comp {j k l} f g := by
    apply CommRingCat.hom_ext
    apply intervalRing_hom_ext (h j)
    intro x
    change intervalRingMap (h j) (h l) (hlo (f.le.trans g.le)) (hhi (f.le.trans g.le))
      (algebraMap V _ x) = intervalRingMap (h k) (h l) (hlo g.le) (hhi g.le)
        (intervalRingMap (h j) (h k) (hlo f.le) (hhi f.le) (algebraMap V _ x))
    simp only [intervalRingMap_algebraMap]

variable {a b : PrimeSpectrum V} (hab : a ≤ b)
variable (ha : ∀ j, lo j ≤ a) (hb : ∀ j, b ≤ hi j)

/-- 区間の共通部分への標準余錐（BM18 Definition 4.6）。 -/
def intervalRingCocone : Cocone (intervalRingDiagram lo hi hlo hhi h) where
  pt := CommRingCat.of (ValuationIntervalRing hab)
  ι :=
    { app := fun j => CommRingCat.ofHom (intervalRingMap (h j) hab (ha j) (hb j))
      naturality := by
        intro j k f
        apply CommRingCat.hom_ext
        apply intervalRing_hom_ext (h j)
        intro x
        change intervalRingMap (h k) hab (ha k) (hb k)
          (intervalRingMap (h j) (h k) (hlo f.le) (hhi f.le) (algebraMap V _ x)) =
            intervalRingMap (h j) hab (ha j) (hb j) (algebraMap V _ x)
        simp only [intervalRingMap_algebraMap] }

variable [Nonempty J] [IsDirectedOrder J]

/-- 区間の縮小する有向族の共通部分は環の余極限を与える（BM18 Definition 4.6）。
下端の合併と、上端の共通部分を、元ごとの条件で表す。 -/
def intervalRingCoconeIsColimit
    (hleft : ∀ x ∈ a.asIdeal, ∃ j, x ∈ (lo j).asIdeal)
    (hright : ∀ x ∉ b.asIdeal, ∃ j, x ∉ (hi j).asIdeal) :
    IsColimit (intervalRingCocone lo hi hlo hhi h hab ha hb) := by
  let F := intervalRingDiagram lo hi hlo hhi h
  let j₀ : J := Classical.choice ‹Nonempty J›
  let along (s : Cocone F) (j : J) : V →+* s.pt :=
    (s.ι.app j).hom.comp (algebraMap V (ValuationIntervalRing (h j)))
  have along_le (s : Cocone F) {j k : J} (hjk : j ≤ k) : along s j = along s k := by
    apply RingHom.ext
    intro x
    have e := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (s.w (homOfLE hjk)))
      (algebraMap V (ValuationIntervalRing (h j)) x)
    change (s.ι.app k) (intervalRingMap (h j) (h k) (hlo hjk) (hhi hjk)
      (algebraMap V (ValuationIntervalRing (h j)) x)) =
      (s.ι.app j) (algebraMap V (ValuationIntervalRing (h j)) x) at e
    rw [intervalRingMap_algebraMap] at e
    exact e.symm
  have along_eq (s : Cocone F) (j : J) : along s j₀ = along s j := by
    obtain ⟨k, h₀k, hjk⟩ := exists_ge_ge j₀ j
    exact (along_le s h₀k).trans (along_le s hjk).symm
  let desc (s : Cocone F) : ValuationIntervalRing hab →+* s.pt :=
    intervalRingLift hab (along s j₀) (fun x hx => by
      obtain ⟨j, hj⟩ := hleft x hx
      rw [along_eq s j]
      change (s.ι.app j) (algebraMap V (ValuationIntervalRing (h j)) x) = 0
      rw [intervalRing_map_eq_zero (h j) hj]
      exact map_zero (s.ι.app j).hom)
      (fun x hx => by
        obtain ⟨j, hj⟩ := hright x hx
        rw [along_eq s j]
        exact (intervalRing_isUnit (h j) hj).map (s.ι.app j).hom)
  refine ⟨fun s => CommRingCat.ofHom (desc s), ?_, ?_⟩
  · intro s j
    apply CommRingCat.hom_ext
    apply intervalRing_hom_ext (h j)
    intro x
    change desc s (intervalRingMap (h j) hab (ha j) (hb j) (algebraMap V _ x)) = along s j x
    rw [intervalRingMap_algebraMap]
    exact (intervalRingLift_algebraMap hab _ _ _ x).trans (DFunLike.congr_fun (along_eq s j) x)
  · intro s m hm
    apply CommRingCat.hom_ext
    apply intervalRing_hom_ext hab
    intro x
    have e := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm j₀))
      (algebraMap V (ValuationIntervalRing (h j₀)) x)
    change m (intervalRingMap (h j₀) hab (ha j₀) (hb j₀) (algebraMap V _ x)) = along s j₀ x at e
    rw [intervalRingMap_algebraMap] at e
    change m (algebraMap V (ValuationIntervalRing hab) x) = desc s (algebraMap V _ x)
    rw [show desc s (algebraMap V (ValuationIntervalRing hab) x) = along s j₀ x from
      intervalRingLift_algebraMap hab _ _ _ x]
    exact e

/-- 一点区間の環はその素点の剰余体（BM18 Definition 4.6）。 -/
def intervalRingPointEquiv (a : PrimeSpectrum V) :
    ValuationIntervalRing (le_rfl : a ≤ a) ≃+* a.asIdeal.ResidueField := by
  let f := algebraMap V a.asIdeal.ResidueField
  let h := (le_rfl : a ≤ a)
  let e := intervalRingLift h f (fun _ hx => (Ideal.algebraMap_residueField_eq_zero).mpr hx)
    (fun x hx =>
      isUnit_iff_ne_zero.mpr (fun he => hx (Ideal.algebraMap_residueField_eq_zero.mp he)))
  let r := Ideal.ResidueField.lift a.asIdeal (algebraMap V (ValuationIntervalRing h))
    (fun _ hx => intervalRing_map_eq_zero h hx) (fun _ hx => intervalRing_isUnit h hx)
  have hr (x : V) : r (algebraMap V a.asIdeal.ResidueField x) =
      algebraMap V (ValuationIntervalRing h) x :=
    Ideal.ResidueField.lift_algebraMap a.asIdeal _ _ _ x
  have he (x : V) : e (algebraMap V (ValuationIntervalRing h) x) =
      algebraMap V a.asIdeal.ResidueField x :=
    intervalRingLift_algebraMap h f _ _ x
  refine RingEquiv.ofRingHom e r ?_ ?_
  · apply IsLocalization.ringHom_ext (M := (V ⧸ a.asIdeal)⁰)
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (r (algebraMap V a.asIdeal.ResidueField y)) = algebraMap V _ y
    rw [hr, he]
  · apply intervalRing_hom_ext h
    intro x
    change r (e (algebraMap V _ x)) = algebraMap V _ x
    rw [he, hr]

@[simp]
theorem intervalRingPointEquiv_algebraMap (a : PrimeSpectrum V) (x : V) :
    intervalRingPointEquiv a (algebraMap V _ x) = algebraMap V a.asIdeal.ResidueField x := by
  simp only [intervalRingPointEquiv, RingEquiv.ofRingHom_apply, intervalRingLift_algebraMap]

/-- 一点に縮む区間の余極限は剰余体（BM18 Proposition 4.8 の証明の (3), (4)）。 -/
def intervalRingColimitIsoResidue (a : PrimeSpectrum V)
    (ha : ∀ j, lo j ≤ a) (hb : ∀ j, a ≤ hi j)
    (hleft : ∀ x ∈ a.asIdeal, ∃ j, x ∈ (lo j).asIdeal)
    (hright : ∀ x ∉ a.asIdeal, ∃ j, x ∉ (hi j).asIdeal)
    [HasColimit (intervalRingDiagram lo hi hlo hhi h)] :
    colimit (intervalRingDiagram lo hi hlo hhi h) ≅ CommRingCat.of a.asIdeal.ResidueField :=
  (colimit.isColimit _).coconePointUniqueUpToIso
      (intervalRingCoconeIsColimit lo hi hlo hhi h le_rfl ha hb hleft hright) ≪≫
    (intervalRingPointEquiv a).toCommRingCatIso

end SerrePositivity
