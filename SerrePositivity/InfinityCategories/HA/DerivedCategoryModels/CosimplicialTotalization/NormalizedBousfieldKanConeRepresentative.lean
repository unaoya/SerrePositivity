module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComparison

/-!
概要：元の Tot の恒等射から、正規化 BK 重みの指定された錐の複体代表を作る。
方針：Hom–Tot 同型と正規化 BK 比較で恒等閉元を移し、零次閉元から実複体射へ戻す。
規約：頂点は元の Tot。native な join 錐への移送は後続の単体的比較で行う。
使われ方：HA 1.2.4、G10 の指定錐の頂点・脚・高次成分の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- Tot への Hom から、同じ係数 Hom 図式の正規化 BK Hom への指定射。 -/
def homToNormalizedBousfieldKan (P : Complex A) (X : CosimplicialObject (Complex A)) :
    homComplex A P ((productTotalFunctor A).obj X) ⟶
      normalizedBousfieldKanHom ((homDiagramFunctor P).obj X) :=
  (homTotalNatIso P).hom.app X ≫
    normalizedBousfieldKanHomComparison ((homDiagramFunctor P).obj X)

/-- 指定比較は元の複体射に対応する閉元を閉元へ送る。 -/
theorem homToNormalizedBousfieldKan_closed (P : Complex A) (X : CosimplicialObject (Complex A))
    (f : P ⟶ (productTotalFunctor A).obj X) :
    δ 0 1 ((homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f)) = 0 := by
  have h := congrArg (fun g => g (Cochain.ofHom f)) ((homToNormalizedBousfieldKan P X).comm 0 1)
  change δ 0 1 ((homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f)) =
    (homToNormalizedBousfieldKan P X).f 1 (δ 0 1 (Cochain.ofHom f)) at h
  simpa using h

/-- 元の Tot への射から作る、同じ正規化重みの実複体射。 -/
def normalizedBousfieldKanRepresentative (P : Complex A) (X : CosimplicialObject (Complex A))
    (f : P ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat ⟶
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) :=
  Cocycle.homOf (Cocycle.mk
    ((homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f)) 1 rfl
    (homToNormalizedBousfieldKan_closed P X f))

/-- 頂点を元の Tot とし、その恒等射から作る指定錐の複体代表。 -/
def normalizedBousfieldKanConeRepresentative (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat ⟶
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) :=
  normalizedBousfieldKanRepresentative _ X (𝟙 _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
