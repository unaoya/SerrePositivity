module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomIso

/-!
概要：Hom と非有界積全複体の比較同型の図式についての自然性。
方針：元の積射影と homFunctor の後合成を成分で照合する。
規約：指定比較鎖写像を保持した自然同型。一般の二重複体を対象とする。
使われ方：HA 1.2.4、G10 の全関手の Hom–Tot 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {A : Type u} [CommRing A] (P : Complex A)
variable {K L : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ)}

/-- 元の二重複体の射に対して、同じ比較鎖写像が可換。 -/
theorem homTotalMap_naturality (f : K ⟶ L) :
    homPostcompose P ((functor (ModuleCat.{u} A)).map f) ≫ homTotalMap P L =
      homTotalMap P K ≫ (functor (ModuleCat.{u} A)).map
        (((homFunctor P).mapHomologicalComplex (.up ℤ)).map f) := by
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
  change ((z.comp (Cochain.ofHom ((functor (ModuleCat.{u} A)).map f)) (add_zero p)).v
      i (i+p) rfl ≫ π L a j (i+p) (by omega)) =
    ((homRowLinear P K p a b hab z).comp (Cochain.ofHom (f.f a)) (add_zero b)).v i j hij
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, homRowLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Cochain.mk_v, Category.assoc, map_π]

/-- Hom と行ごとの Hom の積 Tot の全関手の自然同型。 -/
def homTotalNatIso :
    functor (ModuleCat.{u} A) ⋙ homFunctor P ≅
      (homFunctor P).mapHomologicalComplex (.up ℤ) ⋙ functor (ModuleCat.{u} A) :=
  NatIso.ofComponents (homTotalIso P) (fun f => homTotalMap_naturality P f)

end SerrePositivity.HomologicalAlgebra.ProductTotal
