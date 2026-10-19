module

public import SerrePositivity.KST.DerivedGeometry.ComplexAdjunction
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
概要：加法的随伴を非有界ホモトピー圏の随伴へ降ろす。
方針：複体上の随伴を構成し、ホモトピー同値の局所化との比較同型で随伴を導来化する。
規約：元の関手の完全性や複体の有界性は不要。
使われ方：TT §3・§8、Toën §3.2 の非有界導来随伴の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)

/--
概要：加法的随伴は任意の形状の複体の随伴を与える。
方針：各次数の Hom 同値の両側自然性を使う。
規約：非有界複体も含む。
使われ方：TT §3、Toën §3.2 のホモトピー圏上の随伴。
-/
def adjunctionUnboundedComplex {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adjunctionComplexHomEquiv adj c
      homEquiv_naturality_left_symm := by
        intro K K' L f g
        ext i
        exact adj.homEquiv_naturality_left_symm (f.f i) (g.f i)
      homEquiv_naturality_right := by
        intro K L L' f g
        ext i
        exact adj.homEquiv_naturality_right (f.f i) (g.f i) }

/--
概要：加法的随伴は非有界ホモトピー圏の随伴を与える。
方針：ホモトピー同値の局所化で比較が同型となる導来随伴を構成する。
規約：完全性を要求しない。
使われ方：TT §3・§8、Toën §3.2 の非有界右導来随伴。
-/
def adjunctionHomotopy : F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ) := by
  let W₁ := HomologicalComplex.homotopyEquivalences C (.up ℤ)
  let W₂ := HomologicalComplex.homotopyEquivalences D (.up ℤ)
  let α := (F.mapHomotopyCategoryFactors (.up ℤ)).hom
  let β := (G.mapHomotopyCategoryFactors (.up ℤ)).inv
  have := CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W₁
    (F.mapHomotopyCategory (.up ℤ)) (F.mapHomotopyCategoryFactors (.up ℤ))
  have := CategoryTheory.Functor.isRightDerivedFunctor_of_inverts W₂
    (G.mapHomotopyCategory (.up ℤ)) (G.mapHomotopyCategoryFactors (.up ℤ))
  letI : (F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)).IsLeftDerivedFunctor
      ((CategoryTheory.Functor.associator _ _ _).inv ≫
        CategoryTheory.Functor.whiskerRight α (G.mapHomotopyCategory (.up ℤ))) W₁ :=
    CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts W₁
    (F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ))
    (asIso ((CategoryTheory.Functor.associator _ _ _).inv ≫
      CategoryTheory.Functor.whiskerRight α (G.mapHomotopyCategory (.up ℤ))))
  letI : (G.mapHomotopyCategory (.up ℤ) ⋙ F.mapHomotopyCategory (.up ℤ)).IsRightDerivedFunctor
      (CategoryTheory.Functor.whiskerRight β (F.mapHomotopyCategory (.up ℤ)) ≫
        (CategoryTheory.Functor.associator _ _ _).hom) W₂ :=
    CategoryTheory.Functor.isRightDerivedFunctor_of_inverts W₂
    (G.mapHomotopyCategory (.up ℤ) ⋙ F.mapHomotopyCategory (.up ℤ))
    (asIso (CategoryTheory.Functor.whiskerRight β (F.mapHomotopyCategory (.up ℤ)) ≫
      (CategoryTheory.Functor.associator _ _ _).hom)).symm
  exact (adjunctionUnboundedComplex adj (.up ℤ)).derived W₁ W₂ α β

end SerrePositivity.KST.DerivedGeometry
