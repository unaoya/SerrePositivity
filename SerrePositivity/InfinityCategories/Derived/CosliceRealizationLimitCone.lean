module
public import SerrePositivity.InfinityCategories.Derived.CoslicePrismIso
public import SerrePositivity.InfinityCategories.Derived.CosliceUncurryIso
/-!
概要：弱可縮な全添字上の可逆評価の coslice 実現は、任意後合成後に実極限錐を与える。
方針：保持した全 prism を全錐の関手同型へ移し、指定定値錐から極限性を輸送する。
規約：各脚だけの判定に置き換えない。使われ方：商関手で制限した標準右 Kan 錐の極限性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- coslice の全図式を展開し、任意後合成後に同じ実 join 錐として読む。 -/
def CosliceHomotopyRealization.postcompCone {K X Y : SSet.{u}}
    {x : X _⦋0⦌} {f : K ⟶ X} {H : SSet.Homotopy (SSet.const x) f}
    (R : CosliceHomotopyRealization x f H) (G : X ⟶ Y) : JoinCone (f ≫ G) :=
  ⟨sliceUnderUncurry R.diagram ≫ G, by
    rw [← Category.assoc, sliceUnderUncurry_projection, R.projection]⟩
/-- 可逆な全 prism の同じ coslice 実現は、任意 quasicategory への後合成後も実極限錐。 -/
lemma CosliceHomotopyRealization.postcompCone_isLimit {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {x : X _⦋0⦌} {f : K ⟶ X} {H : SSet.Homotopy (SSet.const x) f}
    (R : CosliceHomotopyRealization x f H)
    (hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated)
    (hK : IsWeaklyContractible K) (G : X ⟶ Y) : IsLimitCone (R.postcompCone G) := by
  obtain ⟨e⟩ := nonempty_functorIso_sliceUnderUncurry (R.prismIso hH)
  have he : FunctorIso (SSet.const (X := join (Δ[0] : SSet.{u}) K) x)
      (sliceUnderUncurry R.diagram) :=
    (congrArg (fun t => FunctorIso t (sliceUnderUncurry R.diagram))
      (sliceUnderUncurry_const_identity K x)).mp e
  have ep := FunctorIso.postcomp he G
  have he' : FunctorIso
      (SSet.const (X := join (Δ[0] : SSet.{u}) K) (G.app (Opposite.op ⦋0⦌) x))
      (sliceUnderUncurry R.diagram ≫ G) :=
    (congrArg (fun t => FunctorIso t (sliceUnderUncurry R.diagram ≫ G))
      (SSet.const_comp x G)).mp ep
  exact IsLimitCone.of_functorIso
    (constantDiagramCone_isLimit K Y hK (G.app (Opposite.op ⦋0⦌) x)) he'
end SerrePositivity.InfinityCategories
