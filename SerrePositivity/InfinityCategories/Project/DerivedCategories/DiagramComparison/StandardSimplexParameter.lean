module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
public import SerrePositivity.EInfinity.BarrattEccles.Normalized

/-!
概要：全単体 Hom 比較のパラメータを、元の小さい標準単体に固定する。
方針：単体を宇宙持ち上げして定数図式とし、既存の正規化関手と同定する。
規約：既存の normalizedFunctor の単体・射を保ち、係数の宇宙だけを合わせる。
使われ方：HA 1.2.4、G10 の正規化テンソル Hom と既存 Dold–Kan 比較の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type v) [Category.{w} J]

/-- 元の小さい標準単体を持ち上げ、添字方向に定数とした全余単体図式。 -/
def liftedStandardSimplexParameter : SimplexCategory ⥤ (J ⥤ SSet.{u}) :=
  SSet.stdSimplex ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) (Type u)).obj uliftFunctor.{u,0} ⋙
      Functor.const J

/-- 持ち上げた標準単体の自由鎖は、既存正規化関手の同じ全余単体図式。 -/
def freeStandardSimplexParameterIso :
    liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J ≅
      SSet.stdSimplex ⋙ SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A ⋙
        Functor.const J :=
  NatIso.ofComponents (fun n => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro i j f
    dsimp [liftedStandardSimplexParameter, freeNegativeChainsDiagramFunctor]
    simp
    change (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map (𝟙 _)) = 𝟙 _
    simp only [CategoryTheory.Functor.map_id])) (by
      intro n m f
      apply NatTrans.ext
      funext j
      simp
      rfl)

/-- テンソル側の標準単体族を、既存正規化関手の同じテンソル族へ戻す。 -/
def freeTensorStandardSimplexIso (X : J ⥤ SSet.{u}) :
    freeTensorFrame A X (liftedStandardSimplexParameter J) ≅
      SSet.stdSimplex ⋙ SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A ⋙
        Functor.const J ⋙ MonoidalCategory.tensorLeft (freeNegativeChainsDiagram (A := A) X) :=
  Functor.isoWhiskerRight (freeStandardSimplexParameterIso A J)
    (MonoidalCategory.tensorLeft (freeNegativeChainsDiagram (A := A) X))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
