module
public import SerrePositivity.KST.SConstruction.SuspensionLoopMappingIso
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityCylinder
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.KST.Spectra.PointedCurryingComponents

/-! # 元の suspension 構造射のパラメータ族
概要：随伴構造射と自然性円筒の全単体を、元の suspension 写像空間へ移す。
方針：写像空間の随伴同型の逆と、その両変数の厳密な自然性を使う。
規約：元の選択空間・円筒・両端の射を保持する。Kan 置換で置き換えない。
使われ方：元の構造射の指定された自然性の族と、高次の合成の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 元の同時選択を suspension 側へ戻した実際の構造射。 -/
def boundaryKanAssemblySigmaAt (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X) ⟶
      (boundaryKanRealizationFunctor (r + 1)).obj X :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _).symm (boundaryKanAssemblyAdjointAt r X v)

/-- 全同時選択の suspension 構造射を、全単体次数で同時に与える族。 -/
def boundaryKanAssemblySigmaFamily (r : ℕ) (X : StableModel.{u}) :
    boundaryKanAssemblyChoices r X ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X))
        ((boundaryKanRealizationFunctor (r + 1)).obj X)).right :=
  boundaryKanAssemblyAdjointFamily r X ≫ (suspensionLoopMappingIso _ _).inv

/-- suspension 側の族は元の選択の構造射を頂点で厳密に回収する。 -/
lemma boundaryKanAssemblySigmaFamily_vertex (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    (boundaryKanAssemblySigmaFamily r X).app (Opposite.op ⦋0⦌) v =
      familyVertex (boundaryKanAssemblySigmaAt r X v) := by
  change (suspensionLoopMappingIso _ _).inv.app _
    ((boundaryKanAssemblyAdjointFamily r X).app _ v) = _
  rw [boundaryKanAssemblyAdjointFamily_vertex, familyVertex_eq_pointedHomVertex]
  exact (suspensionLoopMappingIso_inv_vertex (boundaryKanAssemblyAdjointAt r X v)).trans
    (familyVertex_eq_pointedHomVertex (boundaryKanAssemblySigmaAt r X v)).symm

/-- 元の固定構造射と任意の同時選択の suspension 構造射は同じ成分。 -/
lemma boundaryKanAssemblySigmaAt_component (r : ℕ) (X : StableModel.{u})
    (v : (boundaryKanAssemblyChoices r X) _⦋0⦌) :
    componentOf (boundaryKanAssemblySigma r X) =
      componentOf (boundaryKanAssemblySigmaAt r X v) :=
  componentOf_uncurry (boundaryKanAssemblyAdjointAt_component r X v)

/-- 自然性の元の二重円筒の全単体を suspension 写像空間へ移した族。 -/
def boundaryAssemblySuspensionCylinderFamily (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinder r f ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X))
        ((boundaryKanRealizationFunctor (r + 1)).obj Y)).right :=
  boundaryAssemblyNaturalityCylinderFamily r f ≫ (suspensionLoopMappingIso _ _).inv

/-- 源への制限は、元の suspension 構造射の族の後合成を厳密に回収する。 -/
lemma boundaryAssemblySuspensionCylinderFamily_source (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinderSource r f ≫ boundaryAssemblySuspensionCylinderFamily r f =
      boundaryKanAssemblySigmaFamily r X ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X))
          ((boundaryKanRealizationFunctor (r + 1)).map f)).right := by
  unfold boundaryAssemblySuspensionCylinderFamily boundaryKanAssemblySigmaFamily
  rw [← Category.assoc, boundaryAssemblyNaturalityCylinderFamily_source, Category.assoc]
  have h := congrArg (fun k => boundaryKanAssemblyAdjointFamily r X ≫ k)
    (suspensionLoopMappingIso_inv_post
      (X := (boundaryKanRealizationFunctor r).obj X)
      ((boundaryKanRealizationFunctor (r + 1)).map f)).symm
  change boundaryKanAssemblyAdjointFamily r X ≫
      ((ihom ((boundaryKanRealizationFunctor r).obj X)).map
        ((ihom PointedSimplicialSet.circle.{u}).map
          ((boundaryKanRealizationFunctor (r + 1)).map f))).right ≫
        (suspensionLoopMappingIso _ _).inv =
    (boundaryKanAssemblyAdjointFamily r X ≫ (suspensionLoopMappingIso _ _).inv) ≫
      ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X))).map
        ((boundaryKanRealizationFunctor (r + 1)).map f)).right
  exact h.trans (Category.assoc _ _ _).symm

/-- 標的への制限は、元の suspension 構造射の族の前合成を厳密に回収する。 -/
theorem boundaryAssemblySuspensionCylinderFamily_target (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinderTarget r f ≫ boundaryAssemblySuspensionCylinderFamily r f =
      boundaryKanAssemblySigmaFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj X))
          (Y := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((boundaryKanRealizationFunctor r).obj Y))
          (PointedSimplicialSet.circle.{u} ◁ (boundaryKanRealizationFunctor r).map f)
          ((boundaryKanRealizationFunctor (r + 1)).obj Y)).right :=
  suspensionLoopMappingFamily_prePointed
    (P := boundaryAssemblyNaturalityCylinder r f)
    (Q := boundaryKanAssemblyChoices r Y)
    (X := (boundaryKanRealizationFunctor r).obj X)
    (X' := (boundaryKanRealizationFunctor r).obj Y)
    (Y := (boundaryKanRealizationFunctor (r + 1)).obj Y)
    ((boundaryKanRealizationFunctor r).map f)
    (boundaryKanAssemblyAdjointFamily r Y) (boundaryAssemblyNaturalityCylinderFamily r f)
    (boundaryAssemblyNaturalityCylinderTarget r f)
    (boundaryAssemblyNaturalityCylinderFamily_target r f)

end SerrePositivity.KST.SConstruction
