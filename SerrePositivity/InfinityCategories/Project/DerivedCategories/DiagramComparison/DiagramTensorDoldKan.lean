module
public import SerrePositivity.EInfinity.ComplexLimits.TruncatedDoldKanFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom

/-!
概要：図式テンソルからの全単体 Hom を、図式 Hom 複体の実 Dold–Kan 空間と同定する。
方針：図式の閉随伴と既存の正規化標準単体 Hom 同値を合成する。
規約：単体作用素と添字の自然性条件をともに保持する。
使われ方：HA 1.2.4、G10 の正規化テンソル側から元の Hom 空間への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (P Q : J ⥤ Complex A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 元の正規化標準単体と図式とのテンソルの余単体族。 -/
def normalizedDiagramTensorFrame : SimplexCategory ⥤ (J ⥤ Complex A) :=
  SSet.stdSimplex ⋙ SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A ⋙
    Functor.const J ⋙ tensorLeft P

/-- 図式テンソルの各単体 Hom と、元の図式 Hom の Γ の同値。 -/
def normalizedDiagramTensorHomEquiv (n : SimplexCategory) :
    ((normalizedDiagramTensorFrame A P).obj n ⟶ Q) ≃
      ((truncatedDoldKanFunctor A).obj (linearHomComplex A ((E).obj P) ((E).obj Q))).obj
        (Opposite.op n) :=
  (diagramTensorLinearHomEquiv P Q _).trans
    (normalizedSimplexHomEquiv A (linearHomComplex A ((E).obj P) ((E).obj Q)) n)

/-- 同じ各単体の同値は全単体作用素と可換である。 -/
def normalizedDiagramTensorHomIso :
    (cosimplicialHom (normalizedDiagramTensorFrame A P)).obj Q ≅
      (truncatedDoldKanFunctor A).obj (linearHomComplex A ((E).obj P) ((E).obj Q)) :=
  NatIso.ofComponents (fun n => Equiv.toIso (normalizedDiagramTensorHomEquiv A P Q n.unop)) (by
    intro n m f
    apply ConcreteCategory.hom_ext
    intro g
    change normalizedSimplexHomEquiv A _ m.unop
      (diagramTensorLinearHomEquiv P Q _
        ((P ◁ (Functor.const J).map
          ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
            (SSet.stdSimplex.map f.unop))) ≫ g)) = _
    rw [diagramTensorLinearHomEquiv_precomp]
    exact normalizedSimplexHomEquiv_naturality A _ f.unop _)

/-- 元の自由テンソル族の Hom を、同じ図式 Hom の実 Γ 空間へ戻す。 -/
def freeTensorDiagramHomIso (X : J ⥤ SSet.{u}) :
    (cosimplicialHom (freeTensorFrame A X (liftedStandardSimplexParameter J))).obj Q ≅
      (truncatedDoldKanFunctor A).obj
        (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) X)) ((E).obj Q)) :=
  by
    let e : freeTensorFrame A X (liftedStandardSimplexParameter J) ≅
        normalizedDiagramTensorFrame A (freeNegativeChainsDiagram (A := A) X) :=
      freeTensorStandardSimplexIso A J X
    let e' : (cosimplicialHom (freeTensorFrame A X (liftedStandardSimplexParameter J))).obj Q ≅
        (cosimplicialHom (normalizedDiagramTensorFrame A
          (freeNegativeChainsDiagram (A := A) X))).obj Q :=
      { hom := (cosimplicialHomMap e.inv).app Q
        inv := (cosimplicialHomMap e.hom).app Q
        hom_inv_id := by
          ext n f
          change e.hom.app n.unop ≫ (e.inv.app n.unop ≫ f) = f
          rw [← Category.assoc, e.hom_inv_id_app, Category.id_comp]
        inv_hom_id := by
          ext n f
          change e.inv.app n.unop ≫ (e.hom.app n.unop ≫ f) = f
          rw [← Category.assoc, e.inv_hom_id_app, Category.id_comp] }
    exact e' ≪≫ normalizedDiagramTensorHomIso A (freeNegativeChainsDiagram (A := A) X) Q

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
