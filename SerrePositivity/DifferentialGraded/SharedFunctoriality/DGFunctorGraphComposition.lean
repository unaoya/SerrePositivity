module
public import SerrePositivity.DifferentialGraded.Module.FreeSphere
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 厳密 dg 合成の graph 双加群の実比較
概要：二つの graph の相対 tensor と、元の合成関手の graph を同型で比較する。
方針：代表加群の延長の Yoneda 同型と、右単位の全 Hom 自然性を使う。
規約：導来圏への移行前の実双加群を保つ。使われ方：実 Perf 延長の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- graph tensor の左端パラメータの前合成は、全 Hom 上で厳密に交換する。 -/
lemma bimoduleTensor_precompose_map (P : Bimodule A T E) (Q : Bimodule A E E)
    (x y : D) :
    F.map x y ≫ (BimoduleTensor.compose A T E E P Q).toFunctor.map (F.obj x) (F.obj y) =
      (BimoduleTensor.compose A T E D P (F.comp Q)).toFunctor.map x y := by
  apply moduleHom_ext
  intro t
  change (F.map x y ≫ (BimoduleTensor.compose A T E E P Q).toFunctor.map
      (F.obj x) (F.obj y)) ≫ moduleHomπ A T _ _ t =
    (BimoduleTensor.compose A T E D P (F.comp Q)).toFunctor.map x y ≫
      moduleHomπ A T _ _ t
  have h₁ := BimoduleTensor.compose_leftMap_π A T E E P Q (F.obj x) (F.obj y) t
  have h₂ := BimoduleTensor.compose_leftMap_π A T E D P (F.comp Q) x y t
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => F.map x y ≫ k) h₁).trans
      ((Category.assoc _ _ _).symm.trans h₂.symm))

/-- 各元の D 対象で、graph の合成を合成関手の graph と実同型で比較する。 -/
def dgFunctorGraphCompositionAt (d : D) :
    ForgetEnrichment.of (Complex A)
        ((BimoduleTensor.compose A T E D (functorGraph A E T G)
          (functorGraph A D E F)).rightAt d) ≅
      ForgetEnrichment.of (Complex A) ((functorGraph A D T (F.comp G)).rightAt d) :=
  dgModuleExtensionRepresentableIso A E T G (F.obj d)

/-- graph 合成の比較は、元の D の全 Hom 複体上で自然。 -/
lemma dgFunctorGraphCompositionAt_naturality (x y : D) :
    (BimoduleTensor.compose A T E D (functorGraph A E T G)
        (functorGraph A D E F)).toFunctor.map x y ≫
        moduleHomPostcompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G y).hom =
      (functorGraph A D T (F.comp G)).toFunctor.map x y ≫
        moduleHomPrecompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G x).hom := by
  have hm := bimoduleTensor_precompose_map A D E T F (functorGraph A E T G)
    (Bimodule.diagonal A E) x y
  refine (congrArg (fun k => k ≫ moduleHomPostcompose A T _ _ _
    (dgFunctorGraphCompositionAt A D E T F G y).hom) hm.symm).trans ?_
  have h := congrArg (fun k => F.map x y ≫ k)
    (BimoduleTensor.rightUnitIso_naturality A T E (functorGraph A E T G)
      (F.obj x) (F.obj y))
  dsimp only [functorGraph, DGFunctor.comp, EnrichedFunctor.comp, Bimodule.toFunctor,
    Bimodule.rightAt, dgFunctorGraphCompositionAt, dgModuleExtensionRepresentableIso] at h ⊢
  simp only [Category.assoc] at h ⊢
  convert h using 1 <;> rfl

/-- 元の全 Hom 自然性を持つ、実 graph 双加群の合成同型。 -/
def dgFunctorGraphCompositionIso :
    BimoduleCategory.of A T D
        (BimoduleTensor.compose A T E D (functorGraph A E T G) (functorGraph A D E F)) ≅
      BimoduleCategory.of A T D (functorGraph A D T (F.comp G)) :=
  BimoduleCategory.isoOfFamily A T D (dgFunctorGraphCompositionAt A D E T F G)
    (dgFunctorGraphCompositionAt_naturality A D E T F G)

end SerrePositivity.KST.SConstruction
