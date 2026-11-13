module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementConeExact
public import SerrePositivity.AlgebraicGeometry.CechRefinementConeDouble
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechFunctor
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementNaturality

/-!
概要：各アフィン交叉上の増大 Čech 完全性から、実際の細分写像の H の同型性を得る。
方針：実際の二重 Čech の行の cone に B1 を適用し、零番の行を元の前層へ戻す。
規約：完全性の仮定は交叉上に明示し、準連接性からの供給は幾何の入口で行う。
使われ方：分離的なスキームの準連接層の共通アフィン細分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i))

/-- 各交叉上の完全性から、細分の実際の Čech H の射は同型。
原典 Stacks 30.2.6 のアフィン被覆の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem openCoverCechRefinement_homologyMap_isIso
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι),
      OpenCoverCechAcyclic (openCoverIntersectionPresheaf P
        (cechOpenIntersection U (cechTupleSupport t))) V)
    (hV : ∀ (q : ℕ) (t : Fin (q + 1) → κ),
      OpenCoverCechAcyclic (openCoverIntersectionPresheaf P
        (cechOpenIntersection V (cechTupleSupport t))) V) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q) := by
  let CU := openCoverCechFunctor (R := R) U
  let CV := openCoverCechFunctor (R := R) V
  let A := fun j ↦ CU.obj (openCoverCechResolution P V j)
  let B := fun j ↦ CV.obj (openCoverCechResolution P V j)
  let f := fun j ↦ openCoverCechRefinementMap (openCoverCechResolution P V j) U V ρ hρ
  let a := fun j ↦ CU.map (openCoverCechResolutionDifferential P V j)
  let b := fun j ↦ CV.map (openCoverCechResolutionDifferential P V j)
  have ha : ∀ j, a j ≫ a (j + 1) = 0 := by
    intro j
    change CU.map _ ≫ CU.map _ = 0
    rw [← CU.map_comp, openCoverCechResolutionDifferential_squared, Functor.map_zero]
  have hb : ∀ j, b j ≫ b (j + 1) = 0 := by
    intro j
    change CV.map _ ≫ CV.map _ = 0
    rw [← CV.map_comp, openCoverCechResolutionDifferential_squared, Functor.map_zero]
  have hf : ∀ j, f j ≫ b j = a j ≫ f (j + 1) := fun j ↦
    openCoverCechRefinementMap_naturality U V ρ hρ (openCoverCechResolutionDifferential P V j)
  have hr : ∀ j, 0 < j → SerrePositivity.Cech.RowExact
      (cechRefinementConeGrid A B) (cechRefinementConeHorizontal A B f) j := by
    intro j hj
    have hu := openCoverCechDouble_rowExact P U V ρ hρ j hj
    have hv := openCoverCechDouble_rowExact P V V id (fun _ ↦ le_rfl) j hj
    exact openCoverCechRefinementCone_exact (openCoverCechResolution P V j) U V ρ hρ
      (openCoverCechAcyclic_of_cycles (openCoverCechResolution P V j) U hu.1 hu.2)
      (openCoverCechAcyclic_of_cycles (openCoverCechResolution P V j) V hv.1 hv.2)
  have hA : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (A j).X i)
      (fun i j ↦ ((a j).f i).hom.toAddHom) i := by
    intro i
    exact openCoverCechDouble_colExact P U V (i + 1)
      (fun t ↦ (hU i t).injective_zero) (fun t j ↦ (hU i t).exact j)
  have hB : ∀ i, SerrePositivity.Cech.ColExact (fun i j ↦ (B j).X i)
      (fun i j ↦ ((b j).f i).hom.toAddHom) i := by
    intro i
    exact openCoverCechDouble_colExact P V V (i + 1)
      (fun t ↦ (hV i t).injective_zero) (fun t j ↦ (hV i t).exact j)
  haveI : IsIso (HomologicalComplex.homologyMap (f 0) q) :=
    cechRefinementConeGrid_homologyMap_isIso A B f a b ha hb hf hr hA hB q
  let e := openCoverCechResolutionZeroIso P V
  have hnat := openCoverCechRefinement_homology_naturality U V ρ hρ e.hom q
  haveI : IsIso (fullCechComplexMap (openCoverCechCoefficientMap e.hom U)) := by
    change IsIso (CU.map e.hom)
    infer_instance
  haveI : IsIso (fullCechComplexMap (openCoverCechCoefficientMap e.hom V)) := by
    change IsIso (CV.map e.hom)
    infer_instance
  haveI : IsIso (HomologicalComplex.homologyMap
      (fullCechComplexMap (openCoverCechCoefficientMap e.hom U)) q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).mp inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap
      (fullCechComplexMap (openCoverCechCoefficientMap e.hom V)) q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).mp inferInstance
  haveI : IsIso (HomologicalComplex.homologyMap
      (fullCechComplexMap (openCoverCechCoefficientMap e.hom U)) q ≫
      HomologicalComplex.homologyMap (openCoverCechRefinementMap P U V ρ hρ) q) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
    (fullCechComplexMap (openCoverCechCoefficientMap e.hom U)) q) _

end SerrePositivity.AlgebraicGeometry
