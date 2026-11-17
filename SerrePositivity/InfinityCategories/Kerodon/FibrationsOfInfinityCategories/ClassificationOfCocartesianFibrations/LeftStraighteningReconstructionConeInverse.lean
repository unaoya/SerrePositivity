module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorInverse
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap

/-!
概要：指定復元射の底上の相対逆射で、元の錐を小さい分類模型へ移す。
方針：既存の相対逆射の単位を保持し、その逆射に沿って錐を制限する。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の既存構成の法則。
  元の錐の極限性を仮定せず、頂点を厳密に保つ。制限錐と元の錐の厳密な一致は主張しない。
使われ方：R04のcosliceの普遍錐を、同じ指定復元射の模型上で比較する証明分割。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定復元射の相対逆射に沿う錐の移送は、同じ底と頂点および相対単位を保持する。
Kerodon Tag 028Tの特殊化であり、分類同値そのものの別証明ではない。 -/
@[cite HTT "3.3.2" (partial := special) "既存の相対逆射に沿う錐の制限の法則。"]
lemma leftStraighteningInfinityReconstruction_coneInverse
    {E B D : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (O : B ⟶ D) (c : JoinCone (p ≫ O)) :
    let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
    let r := leftStraighteningInfinityReconstruction p
    ∃ (g : smallLeftUnstraightening (leftStraighteningInfinityDiagram p) ⟶ E)
      (hg : g ≫ p = q),
      Nonempty (VertexIso
        (relativeFunctorVertex p p (r ≫ g)
          (by rw [Category.assoc, hg, leftStraighteningInfinityReconstruction_projection]))
        (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) ∧
      ∃ d : JoinCone (q ≫ O), d.vertex = c.vertex := by
  dsimp only
  obtain ⟨g, hg, hu, _⟩ := exists_relativeFunctorInverse_of_precompositionEquivalence
    p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
    (leftStraighteningInfinityReconstruction p)
    (leftStraighteningInfinityReconstruction_projection p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p)
  refine ⟨g, hg, hu, ?_⟩
  have h : g ≫ (p ≫ O) =
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ O := by
    rw [← Category.assoc, hg]
  exact ⟨(restrictJoinCone c g).cast h,
    (JoinCone.vertex_cast _ h).trans (restrictJoinCone_vertex c g)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
