module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFlatThickTransport
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickLocalization
/-!
概要：Milnor 対角の本質像を同じ cell 平坦商の零対象核として同定する。
方針：実平坦 thick 核を元 gluing へ運び、元対角の thick 本質像判定を適用する。
規約：D-17 の生成判定と D-18 の前三角性・完全性を明示し、元対角を保持する。
使われ方：cell 平坦商の Verdier 列の kernel・localization 欄。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
  [IsDGPretriangulated R (DGOdotGluing R d)]
  [IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal)]
lemma dgGluingMilnorResolvedQuotient_zero_iff
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d)
    (b : (dgNerve R (DGOdotGluing R d)) _⦋0⦌) :
    IsZeroVertex ((dgGluingMilnorResolvedQuotientFunctor R d).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (dgNerve R (DGSmallPerfectBase R (dgAlgebraCategory R d.source))) _⦋0⦌,
        Nonempty (VertexIso ((dgNerve.map (dgOdotQuotientInput R d).diagonal).app
          (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro hb
    obtain ⟨a, ⟨e⟩⟩ := (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R
      (DGOdotGluing R d) (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) b).mp hb
    obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    have hx := dgGluingMilnorDiagonal_flatThick_image R d x.val x.property
    obtain ⟨a, ⟨ea⟩⟩ := (dgGluingMilnorDiagonal_thickClosure_iff_image R d h hgen _).mp hx
    refine ⟨Simplex.vertex (A := R) a, ?_⟩
    erw [dgFunctorNerve_vertex] at e ⊢
    exact ⟨ea.trans e⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨a, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    erw [dgFunctorNerve_vertex] at e
    exact (dgGluingMilnorResolvedQuotient_kills_diagonal R d a).of_vertexIso
      (e.map (dgGluingMilnorResolvedQuotientFunctor R d))
lemma dgGluingMilnorResolvedQuotient_isLocalization
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    IsLocalization (dgGluingMilnorResolvedQuotientFunctor R d)
      (cofiberLocalizingEdges
        {b | ∃ a : (dgNerve R (DGSmallPerfectBase R (dgAlgebraCategory R d.source))) _⦋0⦌,
          Nonempty (VertexIso ((dgNerve.map (dgOdotQuotientInput R d).diagonal).app
            (Opposite.op ⦋0⦌) a) b)}) := by
  have he := Set.ext (fun b =>
    (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) b).symm.trans
        (dgGluingMilnorResolvedQuotient_zero_iff R d h hgen b))
  have hl := resolvedDGQuotientFunctor_isThickLocalization R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
  rw [he] at hl
  exact hl
end SerrePositivity.InfinityCategories
