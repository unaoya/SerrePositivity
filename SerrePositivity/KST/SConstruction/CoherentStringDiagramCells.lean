module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentStringPathFlags
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FunctorReindex

/-! # 元の coherent 図式の合成列を共通対象の豊穣単体へ写す
概要：元の図式の各合成列を、元の各頂点の対象をそのまま持つ豊穣関手として回収する。
方針：coherent nerve の頂点評価で対象を共通化し、全再添字の厳密な等式を証明する。
規約：局所 Kan 性や新しい高次充填を仮定せず、元の図式の全豊穣作用を保持する。
使われ方：元の K prism の Path 族を、端点の固定された native な写像空間へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の coherent 図式の頂点が与える元の対象。 -/
def coherentStringVertexObject
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C) (i : I) : C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (Q.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))

/-- 元の合成列の各対象は、その同じ頂点の像である。 -/
lemma coherentStringCell_object
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {n : ℕ} (s : (nerve I) _⦋n⦌) (i : SimplicialThickening (ULift.{u} (Fin (n + 1)))) :
    (Q.app _ (ULift.up s)).obj i = coherentStringVertexObject Q (s.obj i.as.down) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj]
  have hv : (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i.as.down).op s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj i.as.down) := ComposableArrows.ext₀ rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (Q.app _ (ULift.up
    ((nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i.as.down).op s))) = _
  rw [hv]
  rfl

/-- 同じ元の合成列を、共通の頂点対象を持つ native な豊穣関手として回収する。 -/
def coherentStringDiagramCell
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {n : ℕ} (s : (nerve I) _⦋n⦌) :
    EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 1)))) C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor (Q.app _ (ULift.up s))
    (fun i => coherentStringVertexObject Q (s.obj i.as.down)) (coherentStringCell_object Q s)

/-- 対象の共通化は豊穣関手の前合成と厳密に可換。 -/
lemma coherentString_reobject_precomp {A : Type w} {B : Type u}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} B]
    (R : EnrichedFunctor SSet.{u} A B) (F : EnrichedFunctor SSet.{u} B C)
    (g : B → C) (h : ∀ b, F.obj b = g b) :
    R.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor F g h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor (R.comp SSet F) (fun a => g (R.obj a))
        (fun a => h (R.obj a)) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro a b
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor, eqToHom_refl,
    Category.comp_id, Category.assoc]

/-- 元の図式の各豊穣単体は、全ての面・退化による再添字と厳密に可換。 -/
lemma coherentStringDiagramCell_naturality
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {m n : ℕ} (s : (nerve I) _⦋n⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (SimplicialThickening.functor θ.toOrderHom.uliftMap).comp SSet
      (coherentStringDiagramCell Q s) =
        coherentStringDiagramCell Q ((nerve I).map θ.op s) := by
  rw [coherentStringDiagramCell, coherentString_reobject_precomp]
  have hQ : Q.app (Opposite.op ⦋m⦌) (ULift.up ((nerve I).map θ.op s)) =
      (SimplicialNerve C).map θ.op (Q.app (Opposite.op ⦋n⦌) (ULift.up s)) :=
    congrArg (fun a => a (ULift.up s)) (Q.naturality θ.op)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor_congr _ _ hQ.symm _ _ _

end SerrePositivity.KST.SConstruction
