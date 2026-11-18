module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：余錐の脚と頂点射影の合成則を、ホモトピー圏の任意の射で使う。
方針：任意の射を代表辺で表示し、既存の指定二単体の合成則に戻す。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の既存構成の法則。
使われ方：指定右Kan輸送の比較を、元の辺との両立を保って評価する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 余錐間の任意の射の頂点への射影は、元の各脚との合成式を保つ。 -/
lemma JoinCocone.leg_comp_projection_hom {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d : JoinCocone p)
    (m : (HomotopyCategory.mk c : hoFunctor.obj (sliceUnder p)) ⟶
      HomotopyCategory.mk d) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    Truncated.HomotopyCategory.homMk (c.leg i) ≫
      (hoFunctor.map (sliceUnderProjection p)).toFunctor.map m =
        Truncated.HomotopyCategory.homMk (d.leg i) := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective (X := sliceUnder p) c d m
  exact JoinCocone.leg_comp_projection e i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
