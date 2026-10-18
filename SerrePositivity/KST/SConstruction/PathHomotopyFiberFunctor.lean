module
public import SerrePositivity.KST.SConstruction.PathHomotopyFiberNaturality

/-! # 自然変換の path homotopy fiber の関手化
概要：点つき単体集合に値を持つ自然変換の homotopy fiber を厳密な関手として束ねる。
方針：自然性の正方形を使い、抽象的な関手の恒等・合成法則に帰着する。
規約：入力の圏の宇宙を分ける。使われ方：反復経路境界の大きな定義を展開しない関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 概要：自然変換の path homotopy fiber を入力についての関手に束ねる。
方針：自然性の正方形と、一般の homotopy fiber の恒等・合成法則を使う。
規約：Kan 性や可縮性は不要。使われ方：反復経路境界の fiber 関手。 -/
def pathHomotopyFiberFunctorOfNat {C : Type v} [Category.{w} C]
    {F G : C ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) : C ⥤ PointedSimplicialSet.{u} where
  obj X := pathHomotopyFiber (α.app X)
  map f := pathHomotopyFiberMap _ _ (F.map f) (G.map f) (α.naturality f).symm
  map_id X := by
    simp only [CategoryTheory.Functor.map_id]
    exact pathHomotopyFiberMap_id _ _
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp]
    exact (pathHomotopyFiberMap_comp _ _ _ _ _ _ _ _ _ _).symm

/-- 概要：自然変換の標的の loop から fiber 関手への自然変換。
方針：一般の loop–fiber 比較と正方形についての自然性を束ねる。
規約：点つき写像の厳密な自然性。使われ方：反復経路の自然な比較。 -/
def loopToPathHomotopyFiberNat {C : Type v} [Category.{w} C]
    {F G : C ⥤ PointedSimplicialSet.{u}} (α : F ⟶ G) :
    G ⋙ PointedObject.basedHomFunctor PointedSimplicialSet.circle ⟶
      pathHomotopyFiberFunctorOfNat α where
  app X := loopToPathHomotopyFiber (α.app X)
  naturality {_X _Y} f :=
    (loopToPathHomotopyFiber_naturality _ _ _ _ (α.naturality f).symm).symm

end SerrePositivity.KST.SConstruction
