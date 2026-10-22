module

public import SerrePositivity.EInfinity.ComplexLimits.CodiskHom

/-!
# 各次数の評価と可縮 disk の実随伴

概要：各次数の評価の右随伴を元の可縮 disk で構成する。
方針：元の全 Hom 同値と始域自然性から実関手と随伴を作る。
規約：任意加群と元の加群射を扱う。
使われ方：module epi の実 trivial fibration への移送。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def codiskFunctor (n : ℤ) : ModuleCat.{u} A ⥤ Complex A :=
  Adjunction.rightAdjointOfEquiv (F := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)
    (fun P M => (codiskHomEquiv P M n).symm)
    (fun _ _ M f g => codiskHomEquiv_symm_precomp M n f g)

def codiskAdjunction (n : ℤ) :
    HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n ⊣ codiskFunctor A n :=
  Adjunction.adjunctionOfEquivRight (F := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)
    (fun P M => (codiskHomEquiv P M n).symm)
    (fun _ _ M f g => codiskHomEquiv_symm_precomp M n f g)

lemma codiskFunctor_map_homEquiv (n : ℤ) {M N : ModuleCat.{u} A} (q : M ⟶ N)
    (P : Complex A) (f : P ⟶ codisk M n) :
    codiskHomEquiv P N n (f ≫ (codiskFunctor A n).map q) = codiskHomEquiv P M n f ≫ q :=
  (codiskAdjunction A n).homEquiv_naturality_right_symm f q

end SerrePositivity.EInfinity.ComplexLimits
