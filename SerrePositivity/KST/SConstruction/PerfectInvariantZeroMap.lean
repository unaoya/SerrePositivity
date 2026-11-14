module
public import SerrePositivity.KST.SConstruction.PerfectInvariantSpectrum
public import SerrePositivity.KST.SConstruction.PerfectLocalizingInvariant
public import SerrePositivity.KST.SConstruction.PerfectVerdierRawSquare
public import SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass

/-! # Cat^perf の零関手の不変量値は零射
概要：全対象を零化する同じ完全関手の値は、元の h Sp の零射となる。
方針：元の零安定圏を通る関手との全関手同型と、同じ不変量の零保存を使う。
規約：不変量を全 StableInfinity へ拡張しない。使われ方：Tamme の両射影の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
private lemma perfectTransportedZero {K : Type*} [Category K] [HasZeroMorphisms K]
    {X Y A B : K} (e : X ≅ A) (d : Y ≅ B) :
    e.hom ≫ (0 : A ⟶ B) ≫ d.inv = 0 := by
  simp only [zero_comp, comp_zero]

variable {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

include hF in
/-- 元の全対象を零化する完全関手の Cat^perf 不変量値は、同じ値の間の零射。 -/
lemma IsPerfectLocalizingInvariant.perfectValue_zero_of_zero_values
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hf : ∀ a, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.hom.app (Opposite.op ⦋0⦌) a)) :
    perfectInvariantHoArrow F f hA hB = 0 := by
  let G : A ⟶ B := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory) ≫ fromZeroCategory B
  have hG : ∀ a, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (G.hom.app (Opposite.op ⦋0⦌) a) := by
    intro a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A).hom ≫ (fromZeroCategory B).hom).app _ a)
    rw [throughZero_hom, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex B.obj).isZero
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.hom G.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ hf hG
  have hz : IsZero (perfectInvariantHoObject F
      (perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} perfectZeroCategory_isIdempotentComplete)) :=
    (hF.preservesZero
      (perfectStableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory perfectZeroCategory_isIdempotentComplete)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero).isZeroHo
  calc
    perfectInvariantHoArrow F f hA hB = perfectInvariantHoArrow F G hA hB :=
      perfectInvariantHoArrow_eq_of_functorIso F hA hB e
    _ = perfectInvariantHoArrow F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A) hA
          perfectZeroCategory_isIdempotentComplete ≫
        perfectInvariantHoArrow F (fromZeroCategory B)
          perfectZeroCategory_isIdempotentComplete hB :=
      perfectInvariantHoArrow_comp F _ _ hA perfectZeroCategory_isIdempotentComplete hB
    _ = 0 := by
      rw [hz.eq_zero_of_tgt (perfectInvariantHoArrow F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory A) hA
        perfectZeroCategory_isIdempotentComplete), zero_comp]

include hF in
/-- 元の零関手の同じ BF 表示間の射の類も零である。 -/
lemma IsPerfectLocalizingInvariant.perfectSpectrum_zero_of_zero_values
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hf : ∀ a, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (f.hom.app (Opposite.op ⦋0⦌) a)) :
    perfectInvariantSpectrumHom F f hA hB = 0 := by
  rw [perfectInvariantSpectrumHom, hF.perfectValue_zero_of_zero_values f hA hB hf]
  exact perfectTransportedZero (SpectrumHo.spectrumIso _) (SpectrumHo.spectrumIso _)

end SerrePositivity.KST.SConstruction
