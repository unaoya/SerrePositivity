module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopy
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationVertex

/-!
概要：指定 native 余錐を頂点ホモロジー図式の通常の余錐へ送る。
方針：余錐の全単体ホモトピーとホモトピー圏の自然変換を使う。
規約：余錐の終点は元の実加群の評価ホモロジー。
使われ方：分解の augmentation と filtered ホモロジー余極限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]

lemma dgCoherentConstantHomology_map
    (y : (dgNerve R (RightModule R D)) _⦋0⦌) (x : D) (q : ℤ) {i j : J} (f : i ⟶ j) :
    (dgCoherentBarHomologyDiagram R D
      (SSet.const y : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _) x q).map f =
        𝟙 _ := by
  let e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (dgNerve R (RightModule R D)))
      (PinchedHom.constant y 0) (PinchedHom.constant y 0) := (UniverseEdge.up.{u, max (u + 1) v} (X := nerve J)
    (CategoryTheory.nerve.edgeMk f).toTruncated).map
      ((SSet.truncation 2).map (SSet.const y))
  have he : e = SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj
      (dgNerve R (RightModule R D))) (PinchedHom.constant y 0) := by
    apply SSet.Truncated.Edge.ext
    change PinchedHom.constant y 1 = _
    rw [pinchedConstant_zero]
    exact pinchedConstant_one y
  change (moduleHomotopyHomology R D x q).map
    ((moduleToHomotopy R D).map (DGNerve.HomotopyComparison.edgeClosed e)) = _
  rw [he, DGNerve.HomotopyComparison.edgeClosed_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

def dgCoherentConstantHomologyIso
    (y : (dgNerve R (RightModule R D)) _⦋0⦌) (x : D) (q : ℤ) :
    dgCoherentBarHomologyDiagram R D
      (SSet.const y : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _) x q ≅
        (Functor.const J).obj (((dgNerve.vertexEquiv R (RightModule R D) y).obj
          (Opposite.op x)).homology q) :=
  NatIso.ofComponents (fun j => dgCoherentBarHomologyDiagramObjIso R D (SSet.const y) x q j)
    (by intro i j f; rw [dgCoherentConstantHomology_map]; simp only [Functor.const_obj_map,
      Category.id_comp, Category.comp_id]; rfl)

variable (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentCoconeHomology (c : JoinCocone G) (x : D) (q : ℤ) :
    Cocone (dgCoherentBarHomologyDiagram R D G x q) where
  pt := ((dgNerve.vertexEquiv R (RightModule R D) c.vertex).obj (Opposite.op x)).homology q
  ι := dgCoherentBarHomologyHomotopy R D (F2.coconeTransformationHomotopy c) x q ≫
    (dgCoherentConstantHomologyIso R D c.vertex x q).hom

end SerrePositivity.InfinityCategories
