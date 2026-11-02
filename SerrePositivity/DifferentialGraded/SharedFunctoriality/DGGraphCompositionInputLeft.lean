module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphComposition
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphParameter

/-! # graph 合成比較の左入力に関する全次数自然性
概要：元の代表加群の合成比較は、入力 dg 関手間の全パラメータ自然変換と可換である。
方針：dg Yoneda の延長 Hom を対角双加群の tensor Hom と同定し、右単位の自然性を使う。
規約：閉零変換に限定しない。使われ方：実延長とラベル付き作用の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (E : Type w) (T : Type z)
  [DGCategory A E] [Small.{u} E] [DGCategory A T] [Small.{u} T]
  (G : DGFunctor A E T)

/-- dg Yoneda の実延長の全 Hom は、対角双加群との実 tensor の同じ全 Hom を回収する。 -/
lemma dgModuleExtension_yoneda_map (x y : E) :
    yonedaHom A E x y ≫ (dgModuleExtension A E T G).map
        (representable A x) (representable A y) =
      (BimoduleTensor.compose A T E E (functorGraph A E T G)
        (Bimodule.diagonal A E)).toFunctor.map x y := by
  apply moduleHom_ext
  intro t
  have h₁ := BimoduleTensor.compose_leftMap_π A T E (RightModule A E)
    (functorGraph A E T G) (DGFunctor.id _) (representable A x) (representable A y) t
  have h₂ := BimoduleTensor.compose_leftMap_π A T E E
    (functorGraph A E T G) (Bimodule.diagonal A E) x y t
  simp only [DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp] at h₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => yonedaHom A E x y ≫ k) h₁).trans h₂.symm)

/-- 元の代表加群延長の同型は、元の E の全次数 Hom 複体について自然。 -/
lemma dgModuleExtensionRepresentableIso_naturality (x y : E) :
    yonedaHom A E x y ≫ (dgModuleExtension A E T G).map
        (representable A x) (representable A y) ≫
        moduleHomPostcompose A T _ _ _ (dgModuleExtensionRepresentableIso A E T G y).hom =
      G.map x y ≫ yonedaHom A T (G.obj x) (G.obj y) ≫
        moduleHomPrecompose A T _ _ _ (dgModuleExtensionRepresentableIso A E T G x).hom := by
  rw [← Category.assoc, dgModuleExtension_yoneda_map]
  exact BimoduleTensor.rightUnitIso_naturality A T E (functorGraph A E T G) x y

variable (D : Type v) [DGCategory A D]

/-- 任意 K の左入力変換は、同じ graph 合成比較の前後で全次数に可換。 -/
lemma dgFunctorGraphComposition_input_left {K : Complex A} {F F' : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F F') (d : D) :
    (dgFunctorGraphParameter A D E τ).app d ≫
        (dgModuleExtension A E T G).map (representable A (F.obj d)) (representable A (F'.obj d)) ≫
        moduleHomPostcompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F' G d).hom =
      τ.app d ≫ G.map (F.obj d) (F'.obj d) ≫ yonedaHom A T (G.obj (F.obj d)) (G.obj (F'.obj d)) ≫
        moduleHomPrecompose A T _ _ _ (dgFunctorGraphCompositionAt A D E T F G d).hom := by
  rw [dgFunctorGraphParameter_app, Category.assoc]
  exact congrArg (fun k => τ.app d ≫ k)
    (dgModuleExtensionRepresentableIso_naturality A E T G (F.obj d) (F'.obj d))

end SerrePositivity.KST.SConstruction
