module

public import SerrePositivity.KST.Spectra.WeightTensorCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

/-!
概要：余単体重みの cylinder の二端を与える自然な境界族。
方針：二つの零次面による境界の余積表示を使い、各段の境界族の自然性を証明する。
規約：個々の段で選んだ filler から自然性を推測しない。
使われ方：Goerss–Jardine VII §4。Reedy 持ち上げに渡す図式ホモトピーの境界。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.WeightCylinderBoundary
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 二端の射の可換正方形は cylinder の境界族でも可換。 -/
lemma boundary_naturality {K L X Y : SSet.{u}} (f g : K ⟶ X) (f' g' : L ⟶ Y)
    (a : K ⟶ L) (b : X ⟶ Y) (h₀ : a ≫ f' = f ≫ b) (h₁ : a ≫ g' = g ≫ b) :
    (a ▷ (boundary 1 : SSet.{u})) ≫ boundaryMap f' g' = boundaryMap f g ≫ b := by
  apply (boundaryColimit K).hom_ext
  rintro (_ | _)
  · change (K ◁ boundary.ι (1 : Fin 2)) ≫
      ((a ▷ (boundary 1 : SSet.{u})) ≫ boundaryMap f' g') =
      (K ◁ boundary.ι (1 : Fin 2)) ≫ (boundaryMap f g ≫ b)
    rw [← Category.assoc, whisker_exchange, Category.assoc, boundaryMap_zero,
      ← Category.assoc, whiskerRight_fst, Category.assoc, h₀,
      boundaryMap_zero_assoc]
  · change (K ◁ boundary.ι (0 : Fin 2)) ≫
      ((a ▷ (boundary 1 : SSet.{u})) ≫ boundaryMap f' g') =
      (K ◁ boundary.ι (0 : Fin 2)) ≫ (boundaryMap f g ≫ b)
    rw [← Category.assoc, whisker_exchange, Category.assoc, boundaryMap_one,
      ← Category.assoc, whiskerRight_fst, Category.assoc, h₁,
      boundaryMap_one_assoc]

/-- 両端が同じ射の境界族はパラメーターを忘れる定数族。 -/
lemma boundary_self {K X : SSet.{u}} (f : K ⟶ X) :
    boundaryMap f f = fst K (boundary 1 : SSet.{u}) ≫ f := by
  apply (boundaryColimit K).hom_ext
  rintro (_ | _)
  · change (K ◁ boundary.ι (1 : Fin 2)) ≫ boundaryMap f f =
      (K ◁ boundary.ι (1 : Fin 2)) ≫ (fst K (boundary 1 : SSet.{u}) ≫ f)
    rw [boundaryMap_zero, ← Category.assoc, whiskerLeft_fst]
  · change (K ◁ boundary.ι (0 : Fin 2)) ≫ boundaryMap f f =
      (K ◁ boundary.ι (0 : Fin 2)) ≫ (fst K (boundary 1 : SSet.{u}) ≫ f)
    rw [boundaryMap_one, ← Category.assoc, whiskerLeft_fst]

/-- 二つの自然変換を二端として与える cylinder の境界の自然変換。 -/
def family {F X : CosimplicialObject SSet.{u}} (f g : F ⟶ X) :
    WeightTensorLatching.diagram F (boundary 1 : SSet.{u}) ⟶ X where
  app j := boundaryMap (f.app j) (g.app j)
  naturality i j h := boundary_naturality (f.app i) (g.app i) (f.app j) (g.app j)
    (F.map h) (X.map h) (f.naturality h) (g.naturality h)

/-- cylinder のパラメーターを忘れる自然な射影。 -/
def projection (F : CosimplicialObject SSet.{u}) (A : SSet.{u}) :
    WeightTensorLatching.diagram F A ⟶ F where
  app j := fst (F.obj j) A
  naturality _ _ h := whiskerRight_fst (F.map h) A

/-- 同じ下の射を持つ二つの自然変換の境界族は下で一定になる。 -/
lemma family_projection {F X Y : CosimplicialObject SSet.{u}} (f g : F ⟶ X)
    (p : X ⟶ Y) (h : f ≫ p = g ≫ p) :
    family f g ≫ p = projection F (boundary 1 : SSet.{u}) ≫ f ≫ p := by
  apply NatTrans.ext
  funext j
  change boundaryMap (f.app j) (g.app j) ≫ p.app j =
    fst (F.obj j) (boundary 1 : SSet.{u}) ≫ f.app j ≫ p.app j
  have hj : f.app j ≫ p.app j = g.app j ≫ p.app j := NatTrans.congr_app h j
  have he := boundary_naturality (f.app j) (g.app j)
    (f.app j ≫ p.app j) (g.app j ≫ p.app j) (𝟙 _) (p.app j) (by simp) (by simp)
  simpa only [id_whiskerRight, Category.id_comp, ← hj, boundary_self] using he.symm

end
end SerrePositivity.KST.Spectra.WeightCylinderBoundary
