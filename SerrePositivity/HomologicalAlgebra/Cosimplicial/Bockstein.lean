module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# 余単体的可換環の加法的コホモロジー上の Bockstein

## 概要
加群上の連結写像を台加法群のコホモロジーへ移す。

## 方針
加群から加法可換群への忘却が短複体のホモロジーを保つことを使う。

## 規約
係数環とその構造射は余単体次数に依存しない。

## 使われ方
Hodge–Tate 写像の次数 1。
-/

@[expose] public section
noncomputable section

universe u

open CategoryTheory CategoryTheory.Preadditive

namespace SerrePositivity.Cosimplicial

/-- 概要：加法群としてのコホモロジーと加群としてのホモロジーとの同一視。
方針：台加法群への忘却と交代余面の和が可換で、忘却はホモロジーを保つ。
規約：同じ構造射を持つ余単体的可換環から両方の複体を作る。
使われ方：Bockstein の加法的な表示。 -/
def cohomologyEquivModuleHomology (k : Type u) [CommRing k] (X : CosimplicialObject CommRingCat.{u})
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X) (i : ℕ) :
    cohomology X i ≃+ ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (toModules k X ι)).homology i := by
  let F := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let K := (AlgebraicTopology.alternatingCofaceMapComplex _).obj (toModules k X ι)
  let L := (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  let e : L ≅ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
      intro a b hab
      have hb : b = a + 1 := hab.symm
      subst b
      change (𝟙 (L.X a)) ≫ (_ : L.X a ⟶ L.X (a + 1)) =
        L.d a (a + 1) ≫ 𝟙 (L.X (a + 1))
      erw [Category.id_comp, Category.comp_id]
      change F.map (K.d a (a + 1)) = L.d a (a + 1)
      dsimp only [K, L, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
      rfl)
  exact (((HomologicalComplex.homologyFunctor _ _ i).mapIso e) ≪≫
    (K.sc i).mapHomologyIso F).addCommGroupIsoToAddEquiv

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))

/-- 概要：正則元による商の加法的コホモロジー上の Bockstein。
方針：加群としての連結写像を加法的コホモロジーとの同型で共役する。
規約：余鎖の次数を一つ上げる。
使われ方：Hodge–Tate 写像と cup 積との両立。 -/
def cupBockstein (k : Type u) [CommRing k]
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) (i : ℕ) :
    cohomology (quotPow C d hd_nat 1) i →+ cohomology (quotPow C d hd_nat 1) (i + 1) :=
  let E := cohomologyEquivModuleHomology k (quotPow C d hd_nat 1) (ι ≫ quotProjection C d hd_nat 1)
  (E (i + 1)).symm.toAddMonoidHom.comp
    ((regularBockstein C d hd_nat hd_reg k ι i).hom.toAddMonoidHom.comp (E i).toAddMonoidHom)

end SerrePositivity.Cosimplicial
