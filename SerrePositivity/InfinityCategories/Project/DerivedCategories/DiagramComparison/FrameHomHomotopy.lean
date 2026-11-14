module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameIntervalHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameHomotopyUnderlyingMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameParameterEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterConstant
/-!
概要：指定余作用と同じ鎖ホモトピーから全単体Homのホモトピーを作る。
方針：同じ区間射の単体自然性と両端の余単位則を使う。
規約：IS-W2 A07。全余単体方向の指定ホモトピーを保持する。
使われ方：HA 1.2.4、正規化重みの指定Hom比較の同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "D" => J ⥤ Complex A
local notation "P" => liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J
/-- 指定余作用と全余単体区間評価は元の二射の全単体Homを結ぶ。 -/
def frameHomHomotopyOfInterval {F G : SimplexCategory ⥤ D}
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj ((P).obj ⦋1⦌) ⟶ G)
    (f g : F ⟶ G)
    (hk0 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ k = f)
    (hk1 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ k = g) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q) where
  h := frameHomotopyUnderlyingMap δ k Q
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change frameParameterEvaluation δ k n.unop (SimplexCategory.const n.unop ⦋1⦌ 0) ≫ x = f.app n.unop ≫ x
    rw [frameParameterEvaluation_endpoint δ (standardParameterAugmentation A J) hδ k
      (normalizedIntervalEndpoint A J 0) f hk0 n.unop _ (standardParameter_constant A J n.unop 0)]
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change frameParameterEvaluation δ k n.unop (SimplexCategory.const n.unop ⦋1⦌ 1) ≫ x = g.app n.unop ≫ x
    rw [frameParameterEvaluation_endpoint δ (standardParameterAugmentation A J) hδ k
      (normalizedIntervalEndpoint A J 1) g hk1 n.unop _ (standardParameter_constant A J n.unop 1)]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
local notation "EE" =>
  (Functor.obj (Functor.whiskeringRight SimplexCategory (J ⥤ Complex A)
    (CochainComplex (J ⥤ ModuleCat A) ℤ))
      (functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)) ⋙
    functorToComplexOfFunctors SimplexCategory (J ⥤ ModuleCat A) (ComplexShape.up ℤ))
/-- 指定全余単体鎖ホモトピーを、指定余作用による同じ単体的ホモトピーへ送る。 -/
def frameHomHomotopyOfChainHomotopy (F G : SimplexCategory ⥤ D)
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (f g : F ⟶ G) (h : Homotopy ((EE).map f) ((EE).map g)) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q) :=
  frameHomHomotopyOfInterval δ hδ (frameIntervalHom f g h) f g
    (frameIntervalHom_endpoints f g h).1 (frameIntervalHom_endpoints f g h).2 Q
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
