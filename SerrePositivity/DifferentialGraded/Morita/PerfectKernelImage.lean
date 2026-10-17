module
public import SerrePositivity.DifferentialGraded.Morita.KernelResolution
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectImage
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality

/-! # U16d：通常kernelの各列のperfect性から実際の主Perf作用を構成する

入力の射影解像度と主導来retractの射の計算を使う。kernelの射影性やlocalHomKFlatは追加しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma perfectDGFunctorImage_finiteCell
    (T : DGFunctor A (RightModule A D) (RightModule A E))
    (hgen : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (T.onClosed.obj (ForgetEnrichment.of (Complex A) (representable A d)))))
    {M : ModuleCategory A D} (hM : moduleFiniteCell A D M) :
    modulePerfect A E ((moduleToDerived A E).obj (T.onClosed.obj M)) := by
  let F := T.onClosed
  let Q := moduleToDerived A E
  let G := F ⋙ Q
  let P := modulePerfect A E
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  obtain ⟨c⟩ := hM
  induction c with
  | zero => exact P.prop_of_isZero (Q.map_isZero (F.map_isZero (moduleZero_isZero A D)))
  | generator d _ => exact hgen d
  | @shift M n c ih =>
      exact P.prop_of_iso
        (Q.mapIso (dgModuleFunctorShiftIso A E D T n
          (ForgetEnrichment.to (Complex A) M)) ≪≫ (Q.commShiftIso n).app (F.obj M)).symm
        (P.le_shift n _ ih)
  | @sum M N c d ihc ihd =>
      exact P.prop_of_iso
        (G.mapIso (moduleBiprodIso A D M N) ≪≫ G.mapBiprod M N ≪≫
          biprod.isoProd (G.obj M) (G.obj N)).symm (P.prop_prod _ _ ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact P.prop_of_iso (Q.mapIso (dgModuleFunctorConeIso A D E T f))
        (P.ext_of_isTriangulatedClosed₃ (moduleDerivedConeTriangle A E (F.map f))
          (moduleDerivedConeTriangle_distinguished A E (F.map f)) ihc ihd)
  | iso c e ih => exact P.prop_of_iso (G.mapIso e) ih

lemma perfectDGFunctorImage_projectivePerfect
    (T : DGFunctor A (RightModule A D) (RightModule A E))
    (hgen : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (T.onClosed.obj (ForgetEnrichment.of (Complex A) (representable A d)))))
    {M : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfect A D ((moduleToDerived A D).obj M)) :
    modulePerfect A E ((moduleToDerived A E).obj (T.onClosed.obj M)) := by
  let F := T.onClosed
  let Q := moduleToHomotopy A D
  let Q' := moduleToHomotopy A E
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfect_iff A D _).1 hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  let b : Retract (Q'.obj (F.obj M)) (Q'.obj (F.obj N)) :=
    { i := Q'.map (F.map i)
      r := Q'.map (F.map r)
      retract := by
        have he := congrArg T.onHomotopy.map h
        change Q'.map (F.map (i ≫ r)) = Q'.map (F.map (𝟙 M)) at he
        simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he }
  let L := moduleHomotopyToDerivedClosed A E
  let e := moduleToHomotopyDerivedIso A E
  exact modulePerfectOver_of_retract A E
    ((Retract.ofIso (e.app (F.obj M)).symm).trans
      ((b.map L).trans (Retract.ofIso (e.app (F.obj N)))))
    (perfectDGFunctorImage_finiteCell A D E T hgen hN)

variable (P : Bimodule A E D)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) (P.rightAt d))))

include hP

lemma perfectKernelImage_representable (d : D) :
    modulePerfect A E ((moduleToDerived A E).obj
      ((kernelTensor A D E P).onClosed.obj
        (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  (modulePerfect A E).prop_of_iso
    ((moduleToDerived A E).mapIso (BimoduleTensor.rightUnitIso A E D P d)).symm (hP d)

lemma perfectKernelAction_preserves {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensorOnBimodule A D E P).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  let R := moduleCanonicalProjectiveResolution A D M
  have hR : modulePerfect A D ((moduleToDerived A D).obj R.obj) :=
    (modulePerfect A D).prop_of_iso (moduleDerivedIso A D R.π R.quasiIso).symm hX
  exact (modulePerfect A E).prop_of_iso
    (kernelDerivedTensorOnBimoduleComputation A D E P R).symm
    (perfectDGFunctorImage_projectivePerfect A D E (kernelTensor A D E P)
      (perfectKernelImage_representable A D E P hP) R.projective hR)

def perfectKernelAction : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensorOnBimodule A D E P)
    (fun _ h => perfectKernelAction_preserves A D E P hP h)

def perfectKernelActionInclusionIso :
    perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensorOnBimodule A D E P := Iso.refl _

end SerrePositivity.DifferentialGraded.Morita
