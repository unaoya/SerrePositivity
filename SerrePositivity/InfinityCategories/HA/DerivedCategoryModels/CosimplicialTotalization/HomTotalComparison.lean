module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDoubleComplexComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComponents

/-!
概要：非有界余単体複体の積 Tot と Hom の全関手の自然同型。
方針：一般の二重複体の Hom–Tot 同型と、指定された交代余面・零延長の交換を合成する。
規約：元の積 Tot と Hom 関手を使う。native 極限錐への接続は後続に分ける。
使われ方：HA 1.2.4、G10 の Hom 試験と指定錐の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 入力図式の射も含む、Hom と積 Tot の複体自然同型。 -/
def homTotalNatIso (P : Complex A) :
    productTotalFunctor A ⋙ homFunctor P ≅ homDiagramFunctor P ⋙ productTotalFunctor A :=
  Functor.isoWhiskerLeft (doubleComplexFunctor A)
      (SerrePositivity.HomologicalAlgebra.ProductTotal.homTotalNatIso P) ≪≫
    (homDiagramTotalIso P).symm

/-- 行比較の前向き射は、指定された元の余単体成分と行同型を保つ。 -/
theorem homDiagramTotalIso_hom_π (P : Complex A) (X : CosimplicialObject (Complex A))
    (n : ℕ) (p : ℤ) :
    ((homDiagramTotalIso P).hom.app X).f p ≫
      SerrePositivity.HomologicalAlgebra.ProductTotal.π
        (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj ((doubleComplexFunctor A).obj X))
        n (p-n) p (by omega) =
      componentπ ((homDiagramFunctor P).obj X) n p ≫
        ((homFunctor P).map (rowIso X n).inv).f (p-n) := by
  change ((SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A)).map
    ((homDoubleComplexIso P).hom.app X)).f p ≫ _ = _
  erw [SerrePositivity.HomologicalAlgebra.ProductTotal.map_π
    ((homDoubleComplexIso P).hom.app X) (n : ℤ) (p-n) p (by omega)]
  rw [homDoubleComplexIso_hom_f]
  simp only [HomologicalComplex.comp_f, componentπ, Category.assoc]
  rfl

/-- 逆向きの行比較も、指定射影と元の行同型の Hom 像で計算できる。 -/
theorem homDiagramTotalIso_inv_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (n : ℕ) (p : ℤ) :
    ((homDiagramTotalIso P).inv.app X).f p ≫
      componentπ ((homDiagramFunctor P).obj X) n p =
    SerrePositivity.HomologicalAlgebra.ProductTotal.π
        (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj ((doubleComplexFunctor A).obj X))
        n (p-n) p (by omega) ≫
      ((homFunctor P).map (rowIso X n).hom).f (p-n) := by
  apply (cancel_epi (((homDiagramTotalIso P).hom.app X).f p)).mp
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  have h := ((homDiagramTotalIso P).app X).hom_inv_id
  change (homDiagramTotalIso P).hom.app X ≫ (homDiagramTotalIso P).inv.app X = 𝟙 _ at h
  rw [h, HomologicalComplex.id_f, Category.id_comp]
  rw [← Category.assoc, homDiagramTotalIso_hom_π, Category.assoc,
    ← HomologicalComplex.comp_f, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.id_f]
  erw [Category.comp_id]

/-- 全関手比較の指定成分は、以前に定めた Hom 成分そのもの。 -/
theorem homTotalNatIso_hom_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (n : ℕ) (p : ℤ) :
    ((homTotalNatIso P).hom.app X).f p ≫
      componentπ ((homDiagramFunctor P).obj X) n p =
        ModuleCat.ofHom (homTotalComponent P X p n) := by
  change ((SerrePositivity.HomologicalAlgebra.ProductTotal.homTotalMap P
    ((doubleComplexFunctor A).obj X)).f p ≫
      ((homDiagramTotalIso P).inv.app X).f p) ≫ _ = _
  rw [Category.assoc]
  rw [homDiagramTotalIso_inv_component, ← Category.assoc]
  change (SerrePositivity.HomologicalAlgebra.ProductTotal.homTotalDegreeMap P
    ((doubleComplexFunctor A).obj X) p ≫ _) ≫ _ = _
  rw [SerrePositivity.HomologicalAlgebra.ProductTotal.homTotalDegreeMap_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j hij
  change ((SerrePositivity.HomologicalAlgebra.ProductTotal.homRowLinear P
    ((doubleComplexFunctor A).obj X) p n (p-n) (by omega) z).comp
      (Cochain.ofHom (rowIso X n).hom) (add_zero _)).v i j hij = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
