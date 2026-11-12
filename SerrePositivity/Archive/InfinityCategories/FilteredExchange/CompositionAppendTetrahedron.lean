module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CompositionAppendDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor

/-!
概要：元の二 Hom の全係数と同じ追加射を、一つの実四面体族へ移す。
方針：三単体を二区間の join として読み、係数を左の区間へ制限する。
規約：元の実高次図式を使う。使われ方：指定比較の四面体則への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数を保つ四面体を、二つの実区間の join へ移す元の比較射。 -/
def compositionTetrahedronParameter (P : SSet.{u}) :
    (Δ[3] : SSet.{u}) ⊗ P ⟶ join (Δ[1] ⊗ P) Δ[1] :=
  (β_ Δ[3] P).hom ≫ (P ◁ (joinStdSimplexIso 1 1).inv) ≫
    joinTensorLeft P Δ[1] Δ[1] ≫ joinMap (β_ P Δ[1]).hom (𝟙 Δ[1])

/-- 元の二 Hom と同じ追加射を同時に保持する、単一の実四面体族。 -/
def coherentCompositionAppendTetrahedron
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z W : C) (g : Z ⟶ W) :
    Δ[3] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) ⟶ SimplicialNerve C :=
  compositionTetrahedronParameter _ ≫ coherentCompositionAppendDiagram X Y Z W g

end SerrePositivity.InfinityCategories.F2
