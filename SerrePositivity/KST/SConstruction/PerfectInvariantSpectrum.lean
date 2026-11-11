module
public import SerrePositivity.KST.SConstruction.PerfectInvariantHoArrow
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor

/-! # Cat^perf の同じ不変量値の実 BF 表示
概要：同じ Sp 頂点を BF スペクトルへ戻し、元の値との比較を保持する。
方針：既存の spectrumIso で元の射の類を移し、その同じ類の実 BF 射を取る。
規約：BF 射の厳密合成保存は主張しない。使われ方：Tamme の元の値の実積。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (F : perfectStableInfinity.{u} ⟶ Sp.{u})

/-- 同じ元の不変量値の Sp 頂点を実 BF 対象として表示する。 -/
def perfectInvariantSpectrum (a : perfectStableInfinity.{u} _⦋0⦌) : OmegaSpectrum.{u} :=
  SpectrumHo.spectrum (perfectInvariantHoObject F a)

/-- BF 表示と元の同じ不変量値の対象との比較。 -/
def perfectInvariantSpectrumIso (a : perfectStableInfinity.{u} _⦋0⦌) :
    SpectrumHo.obj (perfectInvariantSpectrum F a) ≅ perfectInvariantHoObject F a :=
  SpectrumHo.spectrumIso _

/-- 元の完全関手の値を、同じ BF 表示の射の類へ移す。 -/
def perfectInvariantSpectrumHom {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    SpectrumHo.obj (perfectInvariantSpectrum F (perfectStableVertex A hA)) ⟶
      SpectrumHo.obj (perfectInvariantSpectrum F (perfectStableVertex B hB)) :=
  SpectrumHo.normalize (perfectInvariantHoArrow F f hA hB)

/-- 同じ BF 表示の射の類は、元の完全関手の合成を保持する。 -/
lemma perfectInvariantSpectrumHom_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C.obj) :
    perfectInvariantSpectrumHom F (show A ⟶ C from (f : A ⟶ B) ≫ (g : B ⟶ C)) hA hC =
      perfectInvariantSpectrumHom F f hA hB ≫ perfectInvariantSpectrumHom F g hB hC := by
  rw [perfectInvariantSpectrumHom, perfectInvariantHoArrow_comp, SpectrumHo.normalize_comp]
  rfl

/-- 同じ BF 表示の射の類は、元の恒等関手を保持する。 -/
lemma perfectInvariantSpectrumHom_id (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) :
    perfectInvariantSpectrumHom F (show A ⟶ A from 𝟙 A) hA hA = 𝟙 _ := by
  rw [perfectInvariantSpectrumHom, perfectInvariantHoArrow_id, SpectrumHo.normalize_id]
  rfl

/-- 同じ元の完全関手の値の類を持つ実 BF 射。 -/
def perfectInvariantSpectrumMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    perfectInvariantSpectrum F (perfectStableVertex A hA) ⟶
      perfectInvariantSpectrum F (perfectStableVertex B hB) :=
  SpectrumHo.representative (perfectInvariantSpectrumHom F f hA hB)

/-- 選んだ実 BF 射は、元の同じ射の類を厳密に回収する。 -/
lemma perfectInvariantSpectrumMap_hom {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj) :
    SpectrumHo.hom (perfectInvariantSpectrumMap F f hA hB) =
      perfectInvariantSpectrumHom F f hA hB := SpectrumHo.hom_representative _

end SerrePositivity.KST.SConstruction
