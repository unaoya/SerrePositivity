module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphComposition
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorIso
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 実 graph 延長の合成比較
概要：反復した実加群延長を、合成 dg 関手の実延長と同型で比較する。
方針：相対 tensor の結合同型と、元の graph 合成同型を全 Hom 自然に合成する。
規約：置換や導来圏の比較を介さない。使われ方：K-4d の Perf 延長の合成法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 実 graph を全加群上で tensor 作用させる、全 Hom 自然な閉零射の関手。 -/
def dgModuleGraphTensorFunctor :
    BimoduleCategory A T D ⥤ BimoduleCategory A T (RightModule A D) :=
  (Functor.prod' (𝟭 (BimoduleCategory A T D))
    ((Functor.const (BimoduleCategory A T D)).obj
      (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _)))) ⋙
    BimoduleTensor.composeFunctor A T D (RightModule A D)

/-- tensor の実結合同型と graph 合成同型からの、全加群上の実比較。 -/
def dgModuleExtensionCompositionTensorIso :
    BimoduleCategory.of A T (RightModule A D)
        (BimoduleTensor.compose A T E (RightModule A D) (functorGraph A E T G)
          (dgModuleExtension A D E F)) ≅
      BimoduleCategory.of A T (RightModule A D) (dgModuleExtension A D T (F.comp G)) :=
  (BimoduleTensor.associatorIso A T E D (RightModule A D)
    (functorGraph A E T G) (functorGraph A D E F) (DGFunctor.id _)).symm ≪≫
    (dgModuleGraphTensorFunctor A D T).mapIso (dgFunctorGraphCompositionIso A D E T F G)

/-- 二回の実延長と tensor 表示の合成作用は、全 Hom 複体上で厳密に一致する。 -/
lemma dgModuleExtension_comp_map (M N : RightModule A D) :
    (dgModuleExtension A D E F).map M N ≫
        (dgModuleExtension A E T G).map
          ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F).obj N) =
      (BimoduleTensor.compose A T E (RightModule A D) (functorGraph A E T G)
        (dgModuleExtension A D E F)).toFunctor.map M N := by
  apply moduleHom_ext
  intro t
  have h₁ := BimoduleTensor.compose_leftMap_π A T E (RightModule A E)
    (functorGraph A E T G) (DGFunctor.id _)
    ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E F).obj N) t
  have h₂ := BimoduleTensor.compose_leftMap_π A T E (RightModule A D)
    (functorGraph A E T G) (dgModuleExtension A D E F) M N t
  simp only [DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp] at h₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (dgModuleExtension A D E F).map M N ≫ k) h₁).trans h₂.symm)

/-- 反復した実 dg 延長から、合成入力の実 dg 延長への元の加群同型。 -/
def dgModuleExtensionCompositionAt (M : RightModule A D) :
    ForgetEnrichment.of (Complex A)
        ((dgModuleExtension A E T G).obj ((dgModuleExtension A D E F).obj M)) ≅
      ForgetEnrichment.of (Complex A) ((dgModuleExtension A D T (F.comp G)).obj M) :=
  (BimoduleCategory.evaluation A T (RightModule A D) M).mapIso
    (dgModuleExtensionCompositionTensorIso A D E T F G)

/-- 実延長の合成比較は、元の全加群の全 Hom 複体について自然。 -/
lemma dgModuleExtensionCompositionAt_naturality (M N : RightModule A D) :
    ((dgModuleExtension A D E F).comp (dgModuleExtension A E T G)).map M N ≫
        moduleHomPostcompose A T _ _ _ (dgModuleExtensionCompositionAt A D E T F G N).hom =
      (dgModuleExtension A D T (F.comp G)).map M N ≫
        moduleHomPrecompose A T _ _ _ (dgModuleExtensionCompositionAt A D E T F G M).hom := by
  have h := (dgModuleExtensionCompositionTensorIso A D E T F G).hom.property M N
  refine (congrArg (fun k => k ≫ moduleHomPostcompose A T _ _ _
    (dgModuleExtensionCompositionAt A D E T F G N).hom)
      (dgModuleExtension_comp_map A D E T F G M N)).trans ?_
  exact h

end SerrePositivity.KST.SConstruction
