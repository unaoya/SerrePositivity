module
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomMap

/-!
概要：非有界積 Tot と線形 Hom の指定比較射の可逆性。
方針：行 Hom の各射影を元の積 Tot へ持ち上げ、次数ごとの両逆を証明する。
規約：前向き射は homTotalMap のまま。全次数の無限積を有限和に置き換えない。
使われ方：HA 1.2.4、G10 の Hom–Tot 比較。
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

/-- 行 Hom の積の元を、元の Tot への次数付き射へ戻す。 -/
def homTotalDegreeInverse (p : ℤ)
    (z : ((functor (ModuleCat.{u} A)).obj
      (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)).X p) :
    Homogeneous P ((functor (ModuleCat.{u} A)).obj K) p :=
  Cochain.mk (fun i j hij => lift K j (fun a b hab =>
    (π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) a (p-a) p (by omega) z).v
      i b (by omega)))

/-- 比較後に逆構成を行うと、元の Tot への射へ戻る。 -/
theorem homTotalDegreeInverse_map (p : ℤ)
    (z : Homogeneous P ((functor (ModuleCat.{u} A)).obj K) p) :
    homTotalDegreeInverse P K p (homTotalDegreeMap P K p z) = z := by
  apply Cochain.ext
  intro i j hij
  subst j
  apply hom_ext K (i+p)
  intro a b hab
  change lift K (i+p) _ ≫ π K a b (i+p) hab = z.v i (i+p) rfl ≫ π K a b (i+p) hab
  rw [lift_π]
  have h := congrArg (fun g => g z) (homTotalDegreeMap_π P K p a (p-a) (by omega))
  change π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)
    a (p-a) p _ (homTotalDegreeMap P K p z) = _ at h
  rw [h]
  rfl

/-- 逆構成後の指定成分を評価すると、元の行 Hom の元へ戻る。 -/
theorem homTotalDegreeMap_inverse (p : ℤ)
    (z : ((functor (ModuleCat.{u} A)).obj
      (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)).X p) :
    homTotalDegreeMap P K p (homTotalDegreeInverse P K p z) = z := by
  apply Concrete.isLimit_ext _ (fanIsLimit
    (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) p)
  rintro ⟨⟨⟨a, b⟩, hab⟩⟩
  change π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) a b p hab
    (homTotalDegreeMap P K p (homTotalDegreeInverse P K p z)) = _
  have h := congrArg (fun g => g (homTotalDegreeInverse P K p z))
    (homTotalDegreeMap_π P K p a b hab)
  change π (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) a b p hab
    (homTotalDegreeMap P K p (homTotalDegreeInverse P K p z)) = _ at h
  rw [h]
  have hb : b = p-a := by omega
  subst b
  apply Cochain.ext
  intro i j hij
  change lift K (i+p) _ ≫ π K a j (i+p) (by omega) = _
  rw [lift_π]
  rfl

/-- 指定比較射と積への持ち上げを両方向に持つ、各次数の線形同値。 -/
def homTotalDegreeEquiv (p : ℤ) :
    Homogeneous P ((functor (ModuleCat.{u} A)).obj K) p ≃ₗ[A]
      ((functor (ModuleCat.{u} A)).obj
        (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K)).X p :=
  { (homTotalDegreeMap P K p).hom with
    invFun := homTotalDegreeInverse P K p
    left_inv := homTotalDegreeInverse_map P K p
    right_inv := homTotalDegreeMap_inverse P K p }

/-- 同じ Hom–Tot 比較射を前向きの射とする複体の同型。 -/
def homTotalIso :
    homComplex A P ((functor (ModuleCat.{u} A)).obj K) ≅
      (functor (ModuleCat.{u} A)).obj (((homFunctor P).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (homTotalDegreeEquiv P K p).toModuleIso)
    (fun p q hpq => by
      have hq : q = p + 1 := hpq.symm
      subst q
      exact homTotalDegreeMap_comm P K p)

/-- 同型への昇格は比較鎖写像そのものを保持する。 -/
theorem homTotalIso_hom : (homTotalIso P K).hom = homTotalMap P K := rfl

end SerrePositivity.HomologicalAlgebra.ProductTotal
