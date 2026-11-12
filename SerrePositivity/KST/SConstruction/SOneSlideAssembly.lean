module
public import SerrePositivity.KST.SConstruction.DiagonalSCyclicInterchange
public import SerrePositivity.KST.SConstruction.MultiDiagonalAssembly

/-! # 元の区間族と S₁ の内外交換の可換性
概要：最内側の S の区間組み立てを、元の最外側の区間組み立てと厳密に比較する。
方針：全順序写像に関する反復交換の自然性を区間の各単体で評価する。
規約：源の交換と標的の巡回交換を明示する。使われ方：境界商上の構造射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の区間組み立ては、源の S₁ 交換と標的の巡回交換を介して最内側の組み立てに一致する。 -/
lemma sOneInnerOuterRealizationIso_assembly (r : ℕ) (X : StableModel.{u}) :
    ((Δ[1] : SSet.{u}) ◁ (sOneInnerOuterRealizationIso r X).hom) ≫
        multiDiagonalAssembly r X =
      diagonalAssembly 1 (iteratedSRealizationDiagram r X) ≫
        (iteratedSRealizationCyclicIso r X).hom := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  let a := (stdSimplex.objEquiv z.1).toOrderHom
  have h := congrArg (fun f => (H.map f).app d z.2)
    (diagonalFixedSInterchangeNatIso_index r d X a)
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app] at h
  change ((multiCoreSConstruction (r + 1) X).map
    (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1))).app d
      ((H.map (((diagonalFixedSInterchangeNatIso 1 r).hom.app d).app X)).app d z.2) =
    (H.map (((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d).app X)).app d
      (((multiRealizationFunctor r).map ((sEndofunctorMap a).app X)).app d z.2)
  have hb : (multiCoreSConstruction (r + 1) X).map
      (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1)) =
      H.map ((sEndofunctorMap a).app (((diagonalSEndofunctor r).obj d).obj X)) := by
    change H.map (((multiSEndofunctor (r + 1)).map
      (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1))).app X) = _
    congr 1
    change ((sEndofunctorMap a).app (((diagonalSEndofunctor r).obj d).obj X) ≫
      (sEndofunctor d.unop.len).map
        (((multiSEndofunctor r).map (𝟙 ((multiIndexDiagonal r).obj d))).app X)) = _
    rw [CategoryTheory.Functor.map_id]
    simp only [NatTrans.id_app]
    change (sEndofunctorMap a).app (((diagonalSEndofunctor r).obj d).obj X) ≫
      (sEndofunctor d.unop.len).map (𝟙 (((diagonalSEndofunctor r).obj d).obj X)) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hb]
  exact h.symm

end SerrePositivity.KST.SConstruction
