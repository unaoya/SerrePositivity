module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFEnrichedFunctor
public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：同じ未完備 native 一四角形を、実 BF スペクトルへ全二胞体ごと送る。
方針：元四頂点像への充満制限と同じ全 Hom の BF 豊穣作用を合成する。
規約：旧公開射を変更しない。使われ方：K-B の有限 BF 四角形と正段比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ BF 写像空間の単体的圏。
方針：元の Ω スペクトルの豊穣を使う。
規約：新しい写像空間を導入しない。使われ方：同じ四角形の coherent nerve。 -/
local instance nativeCoherentBFSquareTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：元未完備 native 一四角形の実 BF スペクトル値全二胞体。
方針：同じ四頂点像の全 Hom を持つ BF 関手を元の全四角形に適用する。
規約：辺だけの別充填を使わない。使われ方：新四辺の同時構成。 -/
def dgKappaNativeCoherentBFSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Sp.{max (u + 1) v} :=
  dgKappaNativeBFFiniteSquare.{u, v} R D I ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFEnrichedFunctor.{u, v} R D I)

end SerrePositivity.KST.SConstruction
