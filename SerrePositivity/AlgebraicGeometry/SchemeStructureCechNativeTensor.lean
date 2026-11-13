module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechBaseChangeIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFlatBaseChange

/-!
概要：実際のスキームの底変換を、複体のテンソル積と Čech H の flat 底変換へ接続する。
方針：有限積とテンソル積の比較を、実際のアフィン切断の比較に合成する。
規約：複体では非 flat な底変換も扱い、H との交換だけに flat を要求する。
使われ方：射影版の形式関数の閉厚化と、五つの比較の底変換。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [DecidableEq ι] [Fintype ι] (U : ι → X.Opens)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))
local instance schemeNativeTensorExtendAdditive :
    (ModuleCat.extendScalars (algebraMap R A)).Additive :=
  projectiveCechTensorExtendAdditive (algebraMap R A)

/-- 実際のアフィン被覆の逆像の Čech 複体と、元の Čech 複体のテンソル積の同型。 -/
def schemeStructureCechNativeTensorComplexIso :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (.up ℕ)).obj
      (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
        ModuleCat.restrictScalars (schemeScalarHom X iX)) U)) ≅
      fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i)) :=
  projectiveCechTensorComplexIso (algebraMap R A)
      (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
        ModuleCat.restrictScalars (schemeScalarHom X iX)) U) ≪≫
    schemeStructureCechBaseChangeComplexIso iX iY g H U hU

/-- 複体の比較は、1 と元の cochain の純テンソルを実際の切断の引き戻しへ送る。 -/
theorem schemeStructureCechNativeTensorComplexIso_unit_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X iX)) U)).X q)
    (t : Fin (q + 1) → ι) :
    (((schemeStructureCechNativeTensorComplexIso iX iY g H U hU).hom.f q).hom
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app _ a)) t =
    ((schemeStructureCechBaseChangeDiagramRestriction (algebraMap R A)
      iX iY g H.w U).app (cechTupleSupport t)).hom (a t) := by
  change (moduleCechScalarExtension (algebraMap R A)
      (schemeStructureCechBaseChangeDiagramRestriction (algebraMap R A) iX iY g H.w U)).app
        (cechTupleSupport t)
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app _ (a t)) = _
  exact moduleCechScalarExtension_one_tmul _ _ _ _

/-- 実際の底変換の構造層の Čech H と、flat なテンソル積の比較。
原典 Stacks 30.5.2(2) の Hⁱ の flat 底変換の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def schemeStructureCechNativeFlatBaseChangeIso (hflat : (algebraMap R A).Flat) (q : ℕ) :
    (ModuleCat.extendScalars (algebraMap R A)).obj
      ((fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
        ModuleCat.restrictScalars (schemeScalarHom X iX)) U)).homology q) ≅
      (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i))).homology q :=
  projectiveCechFlatBaseChangeIso (algebraMap R A)
      (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
        ModuleCat.restrictScalars (schemeScalarHom X iX)) U) hflat q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℕ) q).mapIso
      (schemeStructureCechBaseChangeComplexIso iX iY g H U hU)

end SerrePositivity.AlgebraicGeometry
