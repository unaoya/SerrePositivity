module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorDoldKan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomComponents

/-!
概要：元の自由tensor Hom同型の逆射を同じ各点の逆転置で評価する。
方針：指定標準単体の同型と合成同値の逆射を展開する。
規約：全単体・全次数を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02の指定比較のAW切断成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.EInfinity.ComplexLimits
open scoped TensorProduct
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 標準単体の指定自由tensor同型は各点で恒等射。 -/
theorem freeTensorStandardSimplexIso_hom_app (W : J ⥤ SSet.{u})
    (n : SimplexCategory) (j : J) :
    ((freeTensorStandardSimplexIso A J W).hom.app n).app j = 𝟙 _ := by
  change (𝟙 ((freeNegativeChainsDiagram (A := A) W).obj j) ⊗ₘ
    𝟙 ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n))) = 𝟙 _
  simp only [tensorHom_id, id_whiskerRight]

/-- 指定自由tensor Hom同型の逆射の各点は同じ正規化Hom同値の逆転置。 -/
theorem freeTensorDiagramHomIso_inv_app (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op n)) (j : J) :
    ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op n) α).app j =
      ((diagramTensorLinearHomEquiv (freeNegativeChainsDiagram (A := A) W) Q
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj n))).symm
        ((normalizedSimplexHomEquiv A
          (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
            ((E).obj Q)) n).symm α)).app j := by
  change ((freeTensorStandardSimplexIso A J W).hom.app n).app j ≫ _ = _
  rw [freeTensorStandardSimplexIso_hom_app, Category.id_comp]
  rfl

/-- 元の自由tensor Hom逆射の斉次tensor成分とそのKoszul符号。 -/
theorem freeTensorDiagramHomIso_inv_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op m)) (j : J)
    (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) α).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (((normalizedSimplexHomEquiv A
            (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
              ((E).obj Q)) m).symm α).f q x) j).v i n hn y := by
  rw [freeTensorDiagramHomIso_inv_app]
  exact diagramTensorLinearHomEquiv_symm_component
    (freeNegativeChainsDiagram (A := A) W) Q
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m))
    ((normalizedSimplexHomEquiv A
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q)) m).symm α) j i q n hn y x

/-- Γの射の像の逆転置は、同じ複体射を各パラメータに作用させる。 -/
theorem freeTensorDiagramHomIso_inv_map_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (K : Complex A)
    (g : K ⟶ linearHomComplex A ((E).obj
      (freeNegativeChainsDiagram (A := A) W)) ((E).obj Q))
    (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op m))
    (j : J) (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m)
      (((truncatedDoldKanFunctor A).map g).app (Opposite.op m) α)).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (g.f q (((normalizedSimplexHomEquiv A K m).symm α).f q x)) j).v i n hn y := by
  rw [freeTensorDiagramHomIso_inv_component, normalizedSimplexHomEquiv_symm_map]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
