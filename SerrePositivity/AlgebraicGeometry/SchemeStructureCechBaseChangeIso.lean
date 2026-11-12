module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechBaseChangeCoefficient
public import SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeNativeSections
public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechNonemptyComparison

/-!
概要：実際の底変換の非空アフィン交叉上の比較を、通常の Čech 複体に移す。
方針：自然なテンソル積の射の成分が、切断の canonical な同型であることを示す。
規約：空交叉の切断に対するテンソル積の同型は主張しない。
使われ方：非平坦な閉厚化と、平坦な底変換の共通の複体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [DecidableEq ι] (U : ι → X.Opens)

/-- アフィン交叉の切断の同型を、逆像被覆の対応する交叉まで輸送する。 -/
def schemeStructureCechBaseChangeSectionIso (T : Finset ι)
    (hT : IsAffineOpen (cechOpenIntersection U T)) :
    (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X iX)) U ⋙
        ModuleCat.extendScalars (algebraMap R A)).obj T ≅
      (openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i)).obj T :=
  (schemeAffineBaseChangeNativeSectionsEquiv (algebraMap R A) iX iY g H (cechOpenIntersection U T) hT).toModuleIso ≪≫
    (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars (schemeScalarHom Y iY)).mapIso
      (eqToIso (congrArg op (cechOpenIntersection_scheme_preimage g U T)))

/-- 自然なテンソル積の射のアフィン交叉での成分は、実際の切断の同型。 -/
theorem schemeStructureCechBaseChangeDiagramMap_app (T : Finset ι)
    (hT : IsAffineOpen (cechOpenIntersection U T)) :
    (schemeStructureCechBaseChangeDiagramMap (algebraMap R A) iX iY g H.w U).app T =
      (schemeStructureCechBaseChangeSectionIso iX iY g H U T hT).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change (moduleCechScalarExtension (algebraMap R A)
      (schemeStructureCechBaseChangeDiagramRestriction (algebraMap R A) iX iY g H.w U)).app T
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app _ x) = _
  rw [moduleCechScalarExtension_one_tmul]
  symm
  change ((schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars
      (schemeScalarHom Y iY)).map _).hom
      (schemeAffineBaseChangeNativeSectionsEquiv (algebraMap R A) iX iY g H (cechOpenIntersection U T) hT
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).unit.app _ x)) = _
  rw [schemeAffineBaseChangeNativeSectionsEquiv_unit, Scheme.Hom.appLE_eq_app]
  rfl

/-- 非空アフィン交叉において、実際の係数の底変換の射は同型。 -/
theorem schemeStructureCechBaseChangeDiagramMap_isIso (T : Finset ι)
    (hT : IsAffineOpen (cechOpenIntersection U T)) :
    IsIso ((schemeStructureCechBaseChangeDiagramMap (algebraMap R A) iX iY g H.w U).app T) := by
  rw [schemeStructureCechBaseChangeDiagramMap_app iX iY g H U T hT]
  infer_instance

variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (hU : ∀ i, IsAffineOpen (U i))

/-- 実際の底変換の切断の Čech 複体は、係数をテンソル積にした Čech 複体と同型。
原典 Stacks 30.5.2 の底変換の係数に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。平坦性は複体の比較には不要。 -/
def schemeStructureCechBaseChangeComplexIso :
    fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X iX)) U ⋙
        ModuleCat.extendScalars (algebraMap R A)) ≅
      fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf Y ⋙
        ModuleCat.restrictScalars (schemeScalarHom Y iY)) (fun i ↦ g ⁻¹ᵁ U i)) := by
  let η := schemeStructureCechBaseChangeDiagramMap (algebraMap R A) iX iY g H.w U
  have hη (T : Finset ι) (hT : T.Nonempty) : IsIso (η.app T) :=
    schemeStructureCechBaseChangeDiagramMap_isIso iX iY g H U T
      (cechOpenIntersection_isAffineOpen U hU T hT)
  exact fullCechNonemptyComplexIso (fun T hT ↦ by letI := hη T hT; exact asIso (η.app T))
    (fun hT h ↦ η.naturality (homOfLE h))

end SerrePositivity.AlgebraicGeometry
