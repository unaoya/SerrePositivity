module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Colimit
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
概要：有限表示の代数から剰余体への射を区間に降ろす。
方針：Mathlib の有限表示代数の射の filtered 余極限での因子化を使う。
規約：区間の環は基底環上で比較し、降ろした射も基底環と可換。
使われ方：BM18 Proposition 4.8 の証明 (3), (4) の有限表示模型からの切断。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] {J : Type u} [Preorder J]
variable (lo hi : J → PrimeSpectrum V)
variable (hlo : Monotone lo) (hhi : Antitone hi) (h : ∀ j, lo j ≤ hi j)

/-- 各区間環への基底環からの射をまとめた自然変換。 -/
def intervalRingDiagramUnit :
    (Functor.const J).obj (CommRingCat.of V) ⟶ intervalRingDiagram lo hi hlo hhi h where
  app j := CommRingCat.ofHom (algebraMap V (ValuationIntervalRing (h j)))
  naturality j k f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (intervalRingMap_algebraMap (h j) (h k) (hlo f.le) (hhi f.le) x).symm

variable [Nonempty J] [IsDirectedOrder J]

/-- 有限表示の代数から剰余体への射は、剰余体に縮む区間族の有限段に降りる
（BM18 Proposition 4.8 の証明の (3), (4) に対する有限表示の段）。 -/
theorem exists_intervalRingFactor_of_finitePresentation
    (a : PrimeSpectrum V) (ha : ∀ j, lo j ≤ a) (hb : ∀ j, a ≤ hi j)
    (hleft : ∀ x ∈ a.asIdeal, ∃ j, x ∈ (lo j).asIdeal)
    (hright : ∀ x ∉ a.asIdeal, ∃ j, x ∉ (hi j).asIdeal)
    {S : CommRingCat.{u}} (f : CommRingCat.of V ⟶ S) (hf : f.hom.FinitePresentation)
    (g : S ⟶ CommRingCat.of a.asIdeal.ResidueField)
    (hg : f ≫ g = CommRingCat.ofHom (algebraMap V a.asIdeal.ResidueField)) :
    ∃ (j : J) (g' : S ⟶ (intervalRingDiagram lo hi hlo hhi h).obj j),
      f ≫ g' = (intervalRingDiagramUnit lo hi hlo hhi h).app j ∧
      g = g' ≫ CommRingCat.ofHom (intervalRingMap (h j) le_rfl (ha j) (hb j)) ≫
        (intervalRingPointEquiv a).toCommRingCatIso.hom := by
  let F := intervalRingDiagram lo hi hlo hhi h
  let α := intervalRingDiagramUnit lo hi hlo hhi h
  let c := intervalRingCocone lo hi hlo hhi h le_rfl ha hb
  let hc := intervalRingCoconeIsColimit lo hi hlo hhi h le_rfl ha hb hleft hright
  let e := (intervalRingPointEquiv a).toCommRingCatIso
  have he (i : J) : α.app i ≫ c.ι.app i ≫ e.hom =
      CommRingCat.ofHom (algebraMap V a.asIdeal.ResidueField) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change intervalRingPointEquiv a
      (intervalRingMap (h i) le_rfl (ha i) (hb i) (algebraMap V _ x)) = _
    rw [intervalRingMap_algebraMap, intervalRingPointEquiv_algebraMap]
    rfl
  have hg' (i : J) : f ≫ (g ≫ e.inv) = α.app i ≫ c.ι.app i := by
    apply (cancel_mono e.hom).mp
    calc
      (f ≫ (g ≫ e.inv)) ≫ e.hom = f ≫ g := by
        simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
      _ = CommRingCat.ofHom (algebraMap V a.asIdeal.ResidueField) := hg
      _ = (α.app i ≫ c.ι.app i) ≫ e.hom := by
        simpa only [Category.assoc] using (he i).symm
  obtain ⟨j, g', h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of V) F α f c hc hf (g ≫ e.inv) hg'
  refine ⟨j, g', h₁, ?_⟩
  have hh := congrArg (· ≫ e.hom) h₂
  change g = g' ≫ c.ι.app j ≫ e.hom
  simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hh

end SerrePositivity
