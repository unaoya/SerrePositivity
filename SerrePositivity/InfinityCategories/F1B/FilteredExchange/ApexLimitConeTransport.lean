module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1B.SpecifiedHomotopyLift
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConstantPrism
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoproductPrism
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoproductPrismVertical
public import SerrePositivity.InfinityCategories.F2.CatInfinity.JoinSummands
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PrismHomotopy
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：元の図式を固定し、頂点の指定可逆円柱に沿って極限錐を輸送する。
方針：頂点と図式の和に沿って指定円柱を持ち上げる。
規約：図式上は全時刻で定値、頂点上は元の円柱。使われ方：Kan 比較同値による極限頂点の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定した頂点円柱と定値な元の図式を二因子の和上へ貼る。
方針：coproduct prism。規約：混合単体はこの段階で指定しない。使われ方：頂点輸送の境界。 -/
def apexConeBoundaryPrism {K X : SSet.{u}} (p : K ⟶ X)
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X) :=
  coprodPrism P (snd (Δ[1] : SSet.{u}) K ≫ p)

/-- 概要：指定可逆頂点円柱と元の全図式を保持する、元の図式上の極限錐の輸送。
方針：二因子の和から可逆ホモトピーを延長し、錐全体の同型で極限性を移す。
規約：頂点の射・全図式・全円柱を厳密に保持。使われ方：全空間 Kan 引き戻し錐。 -/
lemma exists_limitCone_of_specifiedApexPrism {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d : JoinCone p) (hd : IsLimitCone d) (a : (Δ[0] : SSet.{u}) ⟶ X)
    (P : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X)
    (h₀ : prismEndpoint 0 (Δ[0] : SSet.{u}) ≫ P = a)
    (h₁ : prismEndpoint 1 (Δ[0] : SSet.{u}) ≫ P = joinInl Δ[0] K ≫ d.val)
    (hP : ∀ x : (Δ[0] : SSet.{u}) _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (P.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        PinchedHom.constant x 1)))) :
    ∃ c : JoinCone p, IsLimitCone c ∧ joinInl Δ[0] K ≫ c.val = a ∧
      ∃ G : SSet.Homotopy c.val d.val,
        (coprod.desc (joinInl Δ[0] K) (joinInr Δ[0] K) ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          (β_ ((Δ[0] : SSet.{u}) ⨿ K) (Δ[1] : SSet.{u})).hom ≫ apexConeBoundaryPrism p P ∧
        ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge G x).toTruncated := by
  let i := coprod.desc (joinInl (Δ[0] : SSet.{u}) K) (joinInr Δ[0] K)
  let f := coprod.desc a p
  have hb₀ : prismEndpoint 0 ((Δ[0] : SSet.{u}) ⨿ K) ≫ apexConeBoundaryPrism p P = f := by
    rw [apexConeBoundaryPrism, coprodPrism_endpoint, h₀, constantPrism_endpoint]
  have hb₁ : prismEndpoint 1 ((Δ[0] : SSet.{u}) ⨿ K) ≫ apexConeBoundaryPrism p P =
      i ≫ d.val := by
    rw [apexConeBoundaryPrism, coprodPrism_endpoint, h₁, constantPrism_endpoint]
    apply coprod.hom_ext <;> simp [i, d.property]
  let Hb := prismHomotopy (apexConeBoundaryPrism p P) hb₀ hb₁
  have hi : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge Hb x).toTruncated := by
    intro x
    refine (isInvertibleEdge_congr
      (e := (simplicialHomotopyVertexEdge Hb x).toTruncated)
      (f := edgeOfSimplex ((apexConeBoundaryPrism p P).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) ?_).mpr ?_
    · exact prismHomotopy_vertical _ hb₀ hb₁ x
    · exact coprodPrism_vertical_isInvertible P _ hP (constantPrism_vertical_isInvertible p) x
  obtain ⟨w, G, hw, hG, hGi⟩ := exists_mono_homotopy_lift_target i f d.val Hb hi
  have hw₀ : joinInl (Δ[0] : SSet.{u}) K ≫ w = a := by
    have h := congrArg (fun t ↦ (coprod.inl : Δ[0] ⟶ Δ[0] ⨿ K) ≫ t) hw
    simpa only [i, f, ← Category.assoc, coprod.inl_desc] using h
  have hw₁ : joinInr (Δ[0] : SSet.{u}) K ≫ w = p := by
    have h := congrArg (fun t ↦ (coprod.inr : K ⟶ Δ[0] ⨿ K) ≫ t) hw
    simpa only [i, f, ← Category.assoc, coprod.inr_desc] using h
  let c : JoinCone p := ⟨w, hw₁⟩
  exact ⟨c, IsLimitCone.of_functorIso hd
    (functorIsoOfPointwiseInvertibleHomotopy G hGi).symm, hw₀, G, hG, hGi⟩

end SerrePositivity.InfinityCategories.F2
