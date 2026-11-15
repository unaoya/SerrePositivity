module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomNaturality
public import SerrePositivity.HomologicalAlgebra.ComplexHomPrecompose

/-!
概要：Hom–Tot 比較の試験対象についての反変自然性。
方針：前合成の自然変換を各行へ適用し、同じ積射影で比較する。
規約：新しい比較同型を選ばず、homTotalMap の両側に指定前合成を使う。
使われ方：HA 1.2.4、G10 の Hom 試験の全パラメーター比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {A : Type u} [CommRing A]

/-- 同じ Hom–Tot 鎖写像は試験対象の前合成とも可換。 -/
theorem homTotalMap_precompose {P Q : Complex A} (g : P ⟶ Q)
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ)) :
    homPrecompose g ((functor (ModuleCat.{u} A)).obj K) ≫ homTotalMap P K =
      homTotalMap Q K ≫ (functor (ModuleCat.{u} A)).map
        (((homPrecomposeNatTrans g).mapHomologicalComplex (.up ℤ)).app K) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply hom_ext _ p
  intro a b hab
  simp only [HomologicalComplex.comp_f, homTotalMap, Category.assoc,
    homTotalDegreeMap_π, map_π, homTotalDegreeMap_π_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j hij
  change (((Cochain.ofHom g).comp z (zero_add p)).v i (i+p) rfl ≫
    π K a j (i+p) (by omega)) =
    ((Cochain.ofHom g).comp (homRowLinear Q K p a b hab z) (zero_add b)).v i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, homRowLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Cochain.mk_v, Category.assoc]

/-- 二重複体を動かす全関手上でも、同じ同型と前合成の正方形が可換。 -/
theorem homTotalNatIso_precompose {P Q : Complex A} (g : P ⟶ Q) :
    Functor.whiskerLeft (functor (ModuleCat.{u} A)) (homPrecomposeNatTrans g) ≫ (homTotalNatIso P).hom =
      (homTotalNatIso Q).hom ≫ Functor.whiskerRight
        ((homPrecomposeNatTrans g).mapHomologicalComplex (.up ℤ)) (functor (ModuleCat.{u} A)) := by
  apply NatTrans.ext
  funext K
  exact homTotalMap_precompose g K

end SerrePositivity.HomologicalAlgebra.ProductTotal
