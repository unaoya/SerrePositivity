module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
概要：完全関手の非有界導来化と全コホモロジーの自然比較。
方針：複体のホモロジー比較を実際の準同型局所化へ降ろす。
規約：導来圏や比較の存在を未証明フィールドにしない。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン係数比較。
-/

@[expose] public section
noncomputable section
universe u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/--
概要：完全関手による複体の像のコホモロジーは元のコホモロジーの像。
方針：各次数の短複体のホモロジー比較を自然に束ねる。
規約：有界性は要求しない。
使われ方：TT §3、Toën §3.2 の非有界比較。
-/
def exactFunctorComplexHomologyIso (n : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F)

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/--
概要：完全関手の導来化は全次数のコホモロジーと自然に可換。
方針：複体の比較を局所化による前合成の全忠実性で降ろす。
規約：既存 mapDerivedCategory の因子分解を保持する。
使われ方：Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の実際の Dqc の比較。
-/
def exactFunctorDerivedHomologyIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F := by
  apply (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (.up ℤ)) D).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors D n) ≪≫
    exactFunctorComplexHomologyIso F n ≪≫
    (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n) _).symm ≪≫
    Functor.associator _ _ _

/--
概要：同型を反映する完全関手の導来化も同型を反映する。
方針：全コホモロジーの自然比較と元の関手の同型反映を使う。
規約：忠実性や導来 Hom の完全忠実性は要求しない。
使われ方：Toën §3.2 のアフィン導来 tilde の保存性。
-/
instance exactFunctorDerived_reflectsIsomorphisms [F.ReflectsIsomorphisms] :
    F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {M N} f _ := by
    apply (DerivedCategory.isIso_iff C f).mpr
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
      (NatIso.isIso_map_iff (exactFunctorDerivedHomologyIso F n) f).mp
        (Functor.map_isIso (DerivedCategory.homologyFunctor D n) (F.mapDerivedCategory.map f))
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C n).map f) F

end SerrePositivity.KST.DerivedGeometry
