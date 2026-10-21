module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeData
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionProjection
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeMap
/-!
概要：同じ比較差の可換四角形から、実分解 Hom 間の全鎖写像を作る。
方針：mapping cocone の同じ実射を使い、二射影と比較 cochain を厳密に保持する。
規約：全次数・全パラメータ上の式。使われ方：分解変更の実 dg 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
variable (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
  G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
    (ForgetEnrichment.of (Complex R) (G.obj y)))
/-- 同じ全 Hom の実入力・半自由出力・比較 cochain を送る実鎖写像。 -/
def dgModuleResolutionChangeHom (X Y : DGModuleFunctorResolutionObject R C E F) :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⟶
      dgModuleFunctorResolutionHomComplex R C E G
        (dgModuleResolutionChangeObject R C E a hs hq X)
        (dgModuleResolutionChangeObject R C E a hs hq Y) :=
  complexMappingCoconeMap (dgModuleFunctorResolutionDifference R C E F X Y)
    (dgModuleFunctorResolutionDifference R C E G
      (dgModuleResolutionChangeObject R C E a hs hq X)
      (dgModuleResolutionChangeObject R C E a hs hq Y))
    (𝟙 _) (moduleHomPostcompose R E X.replacement.val (F.obj Y.source) (G.obj Y.source)
      (a Y.source)) (by
        rw [Category.id_comp]
        exact dgModuleResolutionChange_difference R C E a hs hq ha X Y)
end SerrePositivity.InfinityCategories
