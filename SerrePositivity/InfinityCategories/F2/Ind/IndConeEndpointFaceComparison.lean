module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointReconstructedFace
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulPullbackRight
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointCommaIso

/-!
概要：元の実終点族と再構成された終点族を、同じ実 comma 内で比較する。
方針：元の全底を固定した slice 比較を、充満忠実な元の射影から反映する。
規約：元の両族と元の C 全係数を保持し、充填性を追加仮定にしない。
使われ方：新しい極大点での元の評価族との比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：同じ実終点 comma の slice 射影は充満忠実。
方針：元の Yoneda の充満忠実性を実 slice に沿って移す。規約：追加の仮定なし。
使われ方：元の終点族と再構成された終点族の同じ比較を実 comma に戻す。 -/
lemma indConeEndpointRawSlice_isFullyFaithful :
    IsFullyFaithful (pullback.snd (indYoneda κ C)
      (sliceOverProjection (indConeEndpointPoint κ D))) :=
  fullyFaithful_pullback_snd_of_innerFibration_right (indYoneda_isFullyFaithful κ C)
    (sliceOverProjection (indConeEndpointPoint κ D))
/-- 概要：元の同じ実終点 comma で、元の終点族と再構成された終点族を比較する。
方針：同じ元の底上の slice 比較を充満忠実に反映する。規約：元の両族を保持。
使われ方：新しい極大点での指定評価下の余錐を構成する。 -/
def indConeEndpointRawFaceIso :
    FunctorIso (indConeEndpointRawFace V) (indConeEndpointReconstructedRawFace V) :=
  (indConeEndpointRawSlice_isFullyFaithful (D := D)).preimageFunctorIso (by
    rw [indConeEndpointReconstructedRawFace_slice, ← indConeEndpointSliceCone_source]
    exact indConeEndpointSliceFunctorIso V)
/-- 概要：同じ元の指定評価頂点の標準 comma へも元の比較を移せる。
方針：元の点表示の同型で後合成。規約：元の両全族を保持。使われ方：極大点の共終性。 -/
def indConeEndpointFaceIso :
    FunctorIso (indConeEndpointRawFace V ≫ (indConeEndpointCommaIso κ D).hom)
      (indConeEndpointReconstructedRawFace V ≫ (indConeEndpointCommaIso κ D).hom) :=
  (indConeEndpointRawFaceIso V).postcomp (indConeEndpointCommaIso κ D).hom
end SerrePositivity.InfinityCategories.F2.Ind
