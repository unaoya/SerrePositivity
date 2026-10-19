module

public import SerrePositivity.KST.Spectra.SpectrumNativeLoopFunctor
public import SerrePositivity.KST.Spectra.SpectrumDeloopingComparison

/-!
概要：安定性を仮定せず、Sp の native loop 関手の本質的全射性を証明する。
方針：一段先の対象の実際の loop 四角形を、関手の値と delooping 比較の両方へ結ぶ。
規約：完全忠実性は別工程。使われ方：HA §1.4.2、Sp の loop 関手の同値性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

local instance loopSurjSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance loopSurjHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 関手として選んだ一段先の loop の値と元のスペクトルの具体的な同型。 -/
def nativeLoopTailVertexIso (X : OmegaSpectrum.{u}) :
    VertexIso (nativeLoop.app (Opposite.op ⦋0⦌) (coherentNerveVertex (tail X)))
      (coherentNerveVertex X) :=
  nativeLoopVertexIso (BasedLoop.square (tail X)) ≪≫ (deloopingVertexIso X).symm

/-- 元の Sp の native loop 関手は本質的全射。 -/
lemma nativeLoop_essentiallySurjective : IsEssentiallySurjective nativeLoop.{u} := by
  intro x
  obtain ⟨X, rfl⟩ := (coherentNerveVertexEquiv OmegaSpectrum.{u}).surjective x
  exact ⟨coherentNerveVertex (tail X), ⟨nativeLoopTailVertexIso X⟩⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
