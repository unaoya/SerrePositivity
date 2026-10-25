module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionFiniteKoszulHomologyDiagram
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # 実一元p除算Koszul図式の逐次極限

ℤ次数の当該BS図式を転置し、既存の完全なcolim関手とホモロジー比較を使う。
原典の導来δ基底変更と同定することは、ここではまだ主張しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => deltaPDivisionFiniteKoszulDiagram (σ := σ) D y

/-- BSの実有限Koszul図式を、逐次図式のℤ次数複体へ転置する。 -/
def deltaPDivisionSequentialKoszulDiagramComplex : CochainComplex (ℕ ⥤ ModuleCat.{u} L₀) ℤ where
  X i := F₀ ⋙ eval (ModuleCat.{u} L₀) (.up ℤ) i
  d i j :=
    { app := fun N => ((F₀).obj N).d i j
      naturality := fun _ _ f => ((F₀).map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext N
    exact ((F₀).obj N).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext N
    exact ((F₀).obj N).d_comp_d i j k

/-- BSの当該転置複体のホモロジーは、実各段ホモロジーの図式。 -/
def deltaPDivisionSequentialKoszulDiagramHomologyIso (i : ℤ) :
    (deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y).homology i ≅
      F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i := by
  let K := deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y
  refine NatIso.ofComponents (fun N => ((K.sc i).mapHomologyIso
    ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).symm) ?_
  intro N M f
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i)
    ((evaluation ℕ (ModuleCat.{u} L₀)).map f)
  change homologyMap ((F₀).map f) i =
    ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom ≫
      (K.homology i).map f ≫
      ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj M)).inv at h
  apply (cancel_epi ((K.sc i).mapHomologyIso ((evaluation ℕ (ModuleCat.{u} L₀)).obj N)).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map] using h.symm

/-- 完全な逐次colim関手を用いて各項で作る、実BS図式の極限複体。 -/
def deltaPDivisionSequentialKoszulTermwiseColimit : CochainComplex (ModuleCat.{u} L₀) ℤ :=
  ((colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapHomologicalComplex (.up ℤ)).obj
    (deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y)

/-- 各項で作った実極限は、元の実Koszul図式の圏論的colimitである。 -/
def deltaPDivisionSequentialKoszulTermwiseColimitIso :
    deltaPDivisionSequentialKoszulTermwiseColimit (σ := σ) D y ≅ colimit F₀ :=
  IsColimit.coconePointUniqueUpToIso (isColimitCoconeOfHasColimitEval F₀) (colimit.isColimit F₀)

/-- 当該BS図式の実圏論的colimitのホモロジーは、各段ホモロジーのcolimit。 -/
def deltaPDivisionSequentialKoszulHomologyColimitIso (i : ℤ) :
    (colimit F₀).homology i ≅ colimit (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i) :=
by
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} L₀) := AB5OfSize_of_univLE (ModuleCat.{u} L₀)
  exact
    (homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i).mapIso
      (deltaPDivisionSequentialKoszulTermwiseColimitIso (σ := σ) D y).symm ≪≫
    ((deltaPDivisionSequentialKoszulDiagramComplex (σ := σ) D y).sc i).mapHomologyIso
      (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀) ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapIso
      (deltaPDivisionSequentialKoszulDiagramHomologyIso (σ := σ) D y i)
/-- 実逐次Koszul極限のH⁰は、標準有限商加群図式のcolimitに一致する。 -/
def deltaPDivisionSequentialKoszulH0ColimitIso :
    (colimit F₀).homology 0 ≅ colimit (deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y) :=
  deltaPDivisionSequentialKoszulHomologyColimitIso (σ := σ) D y 0 ≪≫
    (colim : (ℕ ⥤ ModuleCat.{u} L₀) ⥤ ModuleCat.{u} L₀).mapIso
      (deltaPDivisionFiniteKoszulH0DiagramIso (σ := σ) D y)

/-- 正則一元入力では、実逐次Koszul極限は零以外の全次数でホモロジーが零。
無限δ基底変更との同定を仮定して得た結論ではない。 -/
theorem deltaPDivisionSequentialKoszul_isZero_homology
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((colimit F₀).homology i) := by
  have hz : IsZero (colimit (F₀ ⋙ homologyFunctor (ModuleCat.{u} L₀) (.up ℤ) i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro N
    exact (deltaPDivisionFiniteRelations_isKoszulResolution D y hpA hg v hv hy N).isZero i hi
      |>.eq_of_src _ _
  exact hz.of_iso (deltaPDivisionSequentialKoszulHomologyColimitIso (σ := σ) D y i)

end SerrePositivity.BhattScholze
