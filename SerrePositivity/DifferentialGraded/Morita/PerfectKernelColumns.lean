module
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelImage
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable

/-! # 主導来kernelの列のperfect性と、kernelの全導来射に自然なPerf作用

列の評価自体を指定主局所化へ降ろし、通常kernelの代表によらない条件を使う。
U16aの実際の作用関手から主Perfへの制限を構成し、恒等・合成も保つ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

def kernelDerivedColumn (d : D) : Kernel A D E ⥤ DerivedModuleCategory A E :=
  bimoduleDerivedLift A E D (BimoduleCategory.evaluation A E D d ⋙ moduleToDerived A E)
    (fun _ _ f hf => moduleToDerived_inverts A E ((BimoduleCategory.evaluation A E D d).map f)
      (BimoduleCategory.quasiIso_evaluation A E D hf d))

lemma kernelDerivedColumn_fac (d : D) :
    bimoduleToDerived A E D ⋙ kernelDerivedColumn A D E d =
      BimoduleCategory.evaluation A E D d ⋙ moduleToDerived A E :=
  bimoduleDerivedLift_fac A E D _ _

def kernelDerivedColumnComputation (d : D) (P : BimoduleCategory A E D) :
    (kernelDerivedColumn A D E d).obj ((bimoduleToDerived A E D).obj P) ≅
      (moduleToDerived A E).obj ((BimoduleCategory.evaluation A E D d).obj P) :=
  (eqToIso (kernelDerivedColumn_fac A D E d)).app P

def kernelColumnsPerfect : ObjectProperty (Kernel A D E) :=
  fun K => ∀ d : D, modulePerfect A E ((kernelDerivedColumn A D E d).obj K)

lemma kernelColumnsPerfect_ofBimodule_iff (P : BimoduleCategory A E D) :
    kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P) ↔
      ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))) := by
  constructor
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnComputation A D E d P) (h d)
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnComputation A D E d P).symm (h d)

variable [Small.{u} D]

def kernelDerivedColumnActionIso (K : Kernel A D E) (d : D) :
    (kernelDerivedTensor A D E K).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (kernelDerivedColumn A D E d).obj K := by
  obtain ⟨⟨P⟩⟩ := K
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let R := moduleIdentityProjectiveResolution A D M (representable_homotopicallyProjective A D d)
  exact (kernelDerivedTensorOnBimoduleIso A D E P).app ((moduleToDerived A D).obj M) ≪≫
    kernelDerivedTensorOnBimoduleComputation A D E (BimoduleCategory.underlying A E D P) R ≪≫
    (moduleToDerived A E).mapIso
      (BimoduleTensor.rightUnitIso A E D (BimoduleCategory.underlying A E D P) d) ≪≫
    (kernelDerivedColumnComputation A D E d P).symm

lemma perfectDerivedKernelAction_preserves (K : Kernel A D E) (hK : kernelColumnsPerfect A D E K)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E K).obj X) := by
  obtain ⟨⟨P⟩⟩ := K
  have hP := (kernelColumnsPerfect_ofBimodule_iff A D E P).1 hK
  exact (modulePerfect A E).prop_of_iso
    ((kernelDerivedTensorOnBimoduleIso A D E P).app X).symm
    (perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D P) hP hX)

def perfectDerivedKernelAction (K : Kernel A D E) (hK : kernelColumnsPerfect A D E K) :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensor A D E K)
    (fun _ h => perfectDerivedKernelAction_preserves A D E K hK h)

lemma kernelColumnsPerfect_iff_preservesPerfect (K : Kernel A D E) :
    kernelColumnsPerfect A D E K ↔
      ∀ X, modulePerfect A D X → modulePerfect A E ((kernelDerivedTensor A D E K).obj X) := by
  constructor
  · intro hK X hX
    exact perfectDerivedKernelAction_preserves A D E K hK hX
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnActionIso A D E K d)
      (h _ (modulePerfectOver_representable A D d (Set.mem_univ _)))

def perfectDerivedKernelActionInclusionIso (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K) :
    perfectDerivedKernelAction A D E K hK ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensor A D E K := Iso.refl _

/-- kernelの任意の主導来射を、実際のPerf作用間の自然変換へ送る。 -/
def perfectDerivedKernelActionFunctor :
    (kernelColumnsPerfect A D E).FullSubcategory ⥤
      (PerfectModuleCategory A D ⥤ PerfectModuleCategory A E) where
  obj K := perfectDerivedKernelAction A D E K.obj K.property
  map {K L} f := perfectFunctorTransformation A D E _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D E K.obj K.property h)
    (fun _ h => perfectDerivedKernelAction_preserves A D E L.obj L.property h)
    ((kernelDerivedTensorFunctor A D E).map f.hom)
  map_id K := by
    apply NatTrans.ext
    funext X
    apply (modulePerfect A E).hom_ext
    exact NatTrans.congr_app ((kernelDerivedTensorFunctor A D E).map_id K.obj) X.obj
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply (modulePerfect A E).hom_ext
    exact NatTrans.congr_app ((kernelDerivedTensorFunctor A D E).map_comp f.hom g.hom) X.obj

end SerrePositivity.DifferentialGraded.Morita
