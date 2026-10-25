module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.ResolutionDiagram

/-!
概要：元の実導来 ∞ 圏の全 κ-compact 頂点を、同じ選択代表系で被覆する。
方針：標準 resolution の実 κ-filtered 表示を native へ送り、compact retract と swindle を使う。
規約：唯一残す比較引数は D-bar の native/strict 余極限比較。cell 表示の存在はここで供給する。
使われ方：`DGKappaConeInput.covers` と同じ型の D 側供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

lemma dgKappaCone_covers_of_strictFilteredColimitComparison
    (hκ : Cardinal.aleph0 < κ) (comparison : DGKappaStrictFilteredColimitComparison R D κ)
    (y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨P, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let P₀ := ForgetEnrichment.of (Complex R) P.val
  let H := dgModuleDerivedHoComparison R D
  have eP : H.obj (HomotopyCategory.mk (Simplex.vertex P)) ≅
      (moduleToDerived R D).obj P₀ := (moduleToHomotopyDerivedIso R D).app P₀
  let e₀ : VertexIso (dgConeModuleDerivedVertex R D P₀) (Simplex.vertex P) :=
    H.preimageIso (dgConeModuleDerivedVertex_classicalIso R D P₀ ≪≫ eP.symm)
  let eR := dgConeModuleDerivedVertexIsoOfDerivedIso R D
    (moduleDerivedIso R D (moduleResolutionCandidateπ R D P₀)
      (moduleResolutionCandidateπ_quasiIso R D P₀))
  exact dgKappaCovers_of_strictRepresentativePresentation R D κ hκ comparison
    (dgKappaResolutionStrictRepresentativePresentation R D P₀ κ hκ) (eR ≪≫ e₀) hy

end SerrePositivity.InfinityCategories
