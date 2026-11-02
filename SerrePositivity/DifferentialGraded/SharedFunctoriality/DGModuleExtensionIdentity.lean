module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Tensor.Triple

/-! # 実 graph 延長の恒等比較と全 Hom 自然性
概要：恒等 dg 関手の実 graph 延長を元の加群へ同型で比較する。
方針：対角双加群の左単位を用い、全次数 Hom end 上の自然性を保持する。
規約：閉零射だけの自然性で代用しない。使われ方：K-4d の関手的 Perf 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等入力の graph は元の対角双加群。 -/
lemma functorGraph_identity :
    functorGraph A D D (DGFunctor.id D) = Bimodule.diagonal A D := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [functorGraph, DGFunctor.comp, EnrichedFunctor.comp_map,
    DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp, eqToHom_refl, Category.comp_id]

/-- 対角双加群との等号を保つ実 tensor 単位比較。 -/
def dgDiagonalTensorUnitAt (P : Bimodule A D D) (h : P = Bimodule.diagonal A D)
    (M : RightModule A D) :
    ForgetEnrichment.of (Complex A)
        ((BimoduleTensor.compose A D D (RightModule A D) P (DGFunctor.id _)).rightAt M) ≅
      ForgetEnrichment.of (Complex A) M := by
  subst P
  exact BimoduleTensor.leftUnitIso A D (RightModule A D) (DGFunctor.id _) M

/-- 対角との等号で輸送した単位比較も全 Hom について自然。 -/
lemma dgDiagonalTensorUnitAt_naturality (P : Bimodule A D D)
    (h : P = Bimodule.diagonal A D) (M N : RightModule A D) :
    (BimoduleTensor.compose A D D (RightModule A D) P (DGFunctor.id _)).toFunctor.map M N ≫
        moduleHomPostcompose A D _ _ N (dgDiagonalTensorUnitAt A D P h N).hom =
      moduleHomPrecompose A D _ M N (dgDiagonalTensorUnitAt A D P h M).hom := by
  subst P
  exact BimoduleTensor.leftUnitIso_naturality A D (RightModule A D) (DGFunctor.id _) M N

/-- 恒等 dg 関手の実延長を、同じ元の加群へ戻す同型。 -/
def dgModuleExtensionIdentityAt (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) ((dgModuleExtension A D D (DGFunctor.id D)).obj M) ≅
      ForgetEnrichment.of (Complex A) M :=
  dgDiagonalTensorUnitAt A D _ (functorGraph_identity A D) M

/-- 恒等延長の比較は、元の加群の全 Hom 複体について自然。 -/
lemma dgModuleExtensionIdentityAt_naturality (M N : RightModule A D) :
    (dgModuleExtension A D D (DGFunctor.id D)).map M N ≫
        moduleHomPostcompose A D _ _ N (dgModuleExtensionIdentityAt A D N).hom =
      moduleHomPrecompose A D _ M N (dgModuleExtensionIdentityAt A D M).hom :=
  dgDiagonalTensorUnitAt_naturality A D _ (functorGraph_identity A D) M N

end SerrePositivity.KST.SConstruction
