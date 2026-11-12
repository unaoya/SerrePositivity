module

public import SerrePositivity.KST.Spectra.CoherentTrianglePathIso
public import SerrePositivity.KST.Spectra.CoherentSimplexTraces

/-!
概要：元の二単体の長い Hom の作用は、元の Hom 経路から厳密に復元される。
方針：path の区間同型の逆を経路へ前合成し、Hom の射の等式を経路の等式で判定する。
規約：単体の頂点・残る Hom を変えない。使われ方：元の錐と weighted cone の二面の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の経路から復元した長い Hom は、元の二単体の豊穣関手の同じ作用。 -/
lemma triangleTrace_recover (σ : (SimplicialNerve C) _⦋2⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫ triangleTrace σ =
      σ.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ := by
  rw [triangleTrace, ← Category.assoc, trianglePathInterval_maximum_reverse]
  exact Category.id_comp _

/-- path の区間に沿う制限は、元の長い Hom からの射を忠実に検出する。 -/
lemma trianglePathInterval_hom_ext {Y : SSet.{u}}
    {f g : nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶ Y}
    (h : trianglePathInterval ≫ f = trianglePathInterval ≫ g) : f = g := by
  have hp := congrArg (fun k ↦ (trianglePathIntervalIso.{u}).inv ≫ k) h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫ (trianglePathInterval ≫ f) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) ≫ (trianglePathInterval ≫ g) at hp
  simp only [← Category.assoc, trianglePathInterval_maximum_reverse] at hp
  exact (Category.id_comp f).symm.trans (hp.trans (Category.id_comp g))

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
