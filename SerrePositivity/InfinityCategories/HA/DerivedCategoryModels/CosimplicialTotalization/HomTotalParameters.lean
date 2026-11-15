module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalNaturality
public import SerrePositivity.HomologicalAlgebra.ComplexHomPrecompose

/-!
概要：余単体 Hom–Tot 自然同型の試験対象に関する自然性。
方針：全ての元の余単体成分へ射影し、指定 Hom 成分の前合成公式を使う。
規約：図式の射と試験対象の射を同時に保持する。native 錐の普遍性は主張しない。
使われ方：HA 1.2.4、G10 の Hom 試験の全パラメーター比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 試験対象の前合成を全ての余単体図式へ適用する自然変換。 -/
def homDiagramPrecompose {P Q : Complex A} (g : P ⟶ Q) :
    homDiagramFunctor Q ⟶ homDiagramFunctor P where
  app X := Functor.whiskerLeft X (homPrecomposeNatTrans g)
  naturality X Y f := by
    apply NatTrans.ext
    funext n
    exact homPrecompose_postcompose g (f.app n)

/-- 指定 Hom–Tot 自然同型は試験対象の前合成も保つ。 -/
theorem homTotalNatIso_precompose {P Q : Complex A} (g : P ⟶ Q) :
    Functor.whiskerLeft (productTotalFunctor A) (homPrecomposeNatTrans g) ≫
        (homTotalNatIso P).hom =
      (homTotalNatIso Q).hom ≫ Functor.whiskerRight (homDiagramPrecompose g)
        (productTotalFunctor A) := by
  apply NatTrans.ext
  funext X
  apply HomologicalComplex.Hom.ext
  funext p
  apply component_hom_ext ((homDiagramFunctor P).obj X) p
  intro n
  change ((homPrecompose g ((productTotalFunctor A).obj X)).f p ≫
    ((homTotalNatIso P).hom.app X).f p) ≫ _ =
      (((homTotalNatIso Q).hom.app X).f p ≫
        ((productTotalFunctor A).map ((homDiagramPrecompose g).app X)).f p) ≫ _
  rw [Category.assoc, homTotalNatIso_hom_component, Category.assoc,
    componentπ_naturality, ← Category.assoc, homTotalNatIso_hom_component]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact homTotalComponent_precompose g X p n z

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
