module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomDifferential
public import SerrePositivity.HomologicalAlgebra.ComplexHomAdditive

/-!
概要：非有界積全複体への Hom から、行 Hom の積全複体への指定比較射。
方針：同じ積射影を Hom 成分に使い、全微分の二項公式で閉性を示す。
規約：整数の両方向に有界性を課さず、成分の全次数等式を明示する。
使われ方：HA 1.2.4、G10 の Hom–Tot の複体比較。
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
variable (P : Complex A) (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℤ) (.up ℤ))

/-- 全次数等式を明示した行 Hom への線形射影。 -/
def homRowLinear (p a b : ℤ) (hab : a + b = p) :
    Homogeneous P ((functor (ModuleCat.{u} A)).obj K) p →ₗ[A] Homogeneous P (K.X a) b where
  toFun z := Cochain.mk (fun i j hij => z.v i (i + p) rfl ≫ π K a j (i + p) (by omega))
  map_add' z w := by
    apply Cochain.ext
    intro i j hij
    simp [Cochain.mk_v, add_comp]
  map_smul' r z := by
    apply Cochain.ext
    intro i j hij
    simp [Cochain.mk_v, Linear.smul_comp]

/-- 各全次数で同じ行射影を持つ比較射。 -/
def homTotalDegreeMap (p : ℤ) :
    (homComplex A P ((functor (ModuleCat.{u} A)).obj K)).X p ⟶
      ((functor (ModuleCat.{u} A)).obj ((homFunctor P).mapHomologicalComplex (.up ℤ) |>.obj K)).X p :=
  lift _ p (fun a b hab => ModuleCat.ofHom (homRowLinear P K p a b hab))

/-- 比較射を元の行へ射影した成分。 -/
@[reassoc (attr := simp)]
theorem homTotalDegreeMap_π (p a b : ℤ) (hab : a + b = p) :
    homTotalDegreeMap P K p ≫
      π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) a b p hab =
        ModuleCat.ofHom (homRowLinear P K p a b hab) := lift_π _ _ _ _ _ _

/-- 比較射は Hom 微分と積全微分を保つ。 -/
theorem homTotalDegreeMap_comm (p : ℤ) :
    homTotalDegreeMap P K p ≫
      ((functor (ModuleCat.{u} A)).obj (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)).d p (p+1) =
    (homComplex A P ((functor (ModuleCat.{u} A)).obj K)).d p (p+1) ≫
      homTotalDegreeMap P K (p+1) := by
  apply hom_ext _ (p+1)
  intro a b hab
  rw [Category.assoc, d_π, comp_add, Linear.comp_units_smul,
    ← Category.assoc, homTotalDegreeMap_π, ← Category.assoc,
    homTotalDegreeMap_π, Category.assoc, homTotalDegreeMap_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hb : b = p + 1 - a := by omega
  subst b
  change (homRowLinear P K p (a-1) (p+1-a) (by omega) z).comp
      (Cochain.ofHom (K.d (a-1) a)) (add_zero _) +
      a.negOnePow • δ (p+1-a-1) (p+1-a)
        (homRowLinear P K p a (p+1-a-1) (by omega) z) =
      homRowLinear P K (p+1) a (p+1-a) (by omega) (δ p (p+1) z)
  apply Cochain.ext
  intro i j hij
  have h := (homRowComponent_differential_v P K p a z i j hij).symm
  rw [δ_v (p-a) (p+1-a) (by omega) _ i j hij (j-1) (i+1) rfl rfl] at h
  simp only [Cochain.add_v, Cochain.units_smul_v, homRowLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rw [δ_v (p+1-a-1) (p+1-a) (by omega) _ i j hij (j-1) (i+1) rfl rfl]
  simpa only [homRowComponent, Cochain.mk_v] using h

/-- 同じ行射影で定まる Hom–Tot の鎖写像。 -/
def homTotalMap :
    homComplex A P ((functor (ModuleCat.{u} A)).obj K) ⟶
      (functor (ModuleCat.{u} A)).obj (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) where
  f := homTotalDegreeMap P K
  comm' p q hpq := by
    have hq : q = p + 1 := hpq.symm
    subst q
    exact homTotalDegreeMap_comm P K p

end SerrePositivity.HomologicalAlgebra.ProductTotal
