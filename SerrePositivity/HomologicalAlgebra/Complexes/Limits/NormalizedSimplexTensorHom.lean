module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsHomNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.LinearizedSimplexHom
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ConnectiveHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
# 実正規化単体のテンソル Hom と同じ dg Hom の Dold–Kan 各項

概要：元の X⊗N(Δⁿ) から Y への射は同じ dg Hom の実 Dold–Kan 各項と同値。
方針：実閉テンソル随伴・正規化鎖の Hom 同値・同じ自由単体の評価を合成する。
規約：任意可換環・非有界複体・全単体次数を扱う。frame 性と単体集合同型は後続。
使われ方：複体の標準 frame Hom と dg nerve Hom の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

def normalizedSimplexTensor (X : Complex A) : SimplexCategory ⥤ Complex A :=
  SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A ⋙ tensorLeft X

def normalizedSimplexHomEquiv (H : Complex A) (n : SimplexCategory) :
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n) ⟶ H) ≃
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).obj (Opposite.op n) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A (SSet.stdSimplex.obj n) H).trans (_root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A _ n)

def normalizedSimplexTensorHomEquiv (X Y : Complex A) (n : SimplexCategory) :
    ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n ⟶ Y) ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomModule (R := A) (D := Complex A) X Y).obj (Opposite.op n) :=
  (tensorHomEquiv X ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) Y).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homComplex A X Y) n)

lemma normalizedSimplexHomEquiv_naturality (H : Complex A) {n m : SimplexCategory}
    (f : n ⟶ m) (g : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj m) ⟶ H) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H n
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map f) ≫ g) =
        ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).obj
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).map f.op
            (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A H m g) := by
  change _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv A _ n
    (_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv A _ H (_ ≫ g)) = _
  rw [_root_.SerrePositivity.ComplexLimits.normalizedChainsHomEquiv_precomp]
  exact _root_.SerrePositivity.ComplexLimits.linearizedSimplexHomEquiv_naturality A _ f _

def normalizedSimplexTensorHomIso (X Y : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X)).obj Y ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := Complex A) X Y :=
  NatIso.ofComponents (fun n => Equiv.toIso (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorHomEquiv A X Y n.unop)) (by
    intro d e f
    apply ConcreteCategory.hom_ext
    intro α
    change _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A (homComplex A X Y) e.unop
      (tensorHomEquiv X _ Y ((X ◁ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
        (SSet.stdSimplex.map f.unop)) ≫ α)) = _
    rw [tensorHomEquiv_naturality_source]
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_naturality A (homComplex A X Y) f.unop _)

end SerrePositivity.ComplexLimits
