module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopy
public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyEdgeNaturality

/-!
概要：coherent ホモロジー比較の各成分は、元の指定垂直辺のホモロジー射。
方針：道によるホモトピー圏から辺による模型へ同じ代表を戻す。
規約：分解の augmentation を任意の同型に置き換えない。
使われ方：頂点ごとの擬同型性による自然同型の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgBarHomotopyNatTrans₂_app {X Y : SSet.{w}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (h : SSet.Homotopy f g) (x : X _⦋0⦌) :
    (dgBarHomotopyNatTrans₂ h).app ⟨x⟩ =
      SSet.Truncated.HomotopyCategory₂.homMk (simplicialHomotopyVertexEdge h x).toTruncated := by
  change (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
    ((homotopyNatTransOfEndpoints h.h h.h₀ h.h₁).app (SSet.HomotopyCategory.mk x)) = _
  rw [F2.homotopyNatTransOfEndpoints_app, dgBarPathToEdge_homMk]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  {G H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D)}

lemma dgCoherentBarHomologyHomotopy_app (h : SSet.Homotopy G H) (x : D) (q : ℤ) (j : J) :
    (dgCoherentBarHomologyHomotopy R D h x q).app j ≫
        (dgCoherentBarHomologyDiagramObjIso R D H x q j).hom =
      (dgCoherentBarHomologyDiagramObjIso R D G x q j).hom ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
          (DGNerve.HomotopyComparison.edgeClosed
            (simplicialHomotopyVertexEdge h (ULift.up (nerveEquiv.symm j))).toTruncated)) q := by
  change (moduleHomotopyHomology R D x q).map
      ((DGNerve.HomotopyComparison.toH0 R (RightModule R D)).map
        ((dgBarHomotopyNatTrans₂ h).app ⟨ULift.up (nerveEquiv.symm j)⟩)) ≫ _ = _
  rw [dgBarHomotopyNatTrans₂_app, DGNerve.HomotopyComparison.toH0_homMk]
  exact (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).hom.naturality
    ((moduleEvaluation R D x).map
      (DGNerve.HomotopyComparison.edgeClosed
        (simplicialHomotopyVertexEdge h (ULift.up (nerveEquiv.symm j))).toTruncated))

end SerrePositivity.InfinityCategories
