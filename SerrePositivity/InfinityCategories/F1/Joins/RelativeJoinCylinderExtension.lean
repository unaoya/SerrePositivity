module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderMono
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinderEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：単射の写像円柱上の射を relative join 全体へ延長する。
方針：比較の単射性と前合成の同値性から、制限の trivial Kan fibration 性を使う。
規約：標的のみ quasicategory とし、構造射の両端の充填性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、区間上の全空間比較への準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 join 上の関手の円柱への制限は trivial Kan fibration。
方針：単射である前合成の同値条件の一般定理を使う。
規約：標的 E は quasicategory、構造射 f は単射。
使われ方：Kerodon Theorem 5.2.4.1、パラメーターを持つ延長とその一意性。 -/
instance relativeJoinCylinderComparison_pre_trivialKanFibration
    {X Y E : SSet.{u}} (f : X ⟶ Y) [Mono f] [Quasicategory E] :
    TrivialKanFibration ((pre (relativeJoinCylinderComparison f)).app E) :=
  (isPrecompositionEquivalence_relativeJoinCylinderComparison f).trivialKanFibration_pre E

/-- 概要：指定した円柱上の射の relative join への延長の空間。
方針：関手単体集合の制限の指定頂点上の fiber を取る。
規約：射の等式で円柱上の制限を固定する。
使われ方：Kerodon Theorem 5.2.4.1、延長の選択の可縮性。 -/
noncomputable def relativeJoinCylinderExtensionSpace {X Y E : SSet.{u}} (f : X ⟶ Y)
    (u : pushout (prismEndpoint 1 X) f ⟶ E) : SSet.{u} :=
  vertexFiber ((pre (relativeJoinCylinderComparison f)).app E) (functorVertex u)

/-- 概要：単射の円柱上の射の延長の空間は可縮な Kan 複体。
方針：制限の trivial Kan fibration 性から fiber の境界充填を得る。
規約：標的 E 以外には quasicategory 性を要求しない。
使われ方：Kerodon Theorem 5.2.4.1、延長の存在と整合的な一意性。 -/
lemma relativeJoinCylinderExtensionSpace_isContractibleKan
    {X Y E : SSet.{u}} (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (u : pushout (prismEndpoint 1 X) f ⟶ E) :
    IsContractibleKan (relativeJoinCylinderExtensionSpace f u) :=
  vertexFiber_isContractibleKan _ _

/-- 概要：単射の円柱上の射は relative join 全体へ厳密に延長できる。
方針：前合成の本質的全射性を単射上の厳密な頂点全射性へ移す。
規約：制限は関手の同型ではなく射の等式として固定する。
使われ方：Kerodon Theorem 5.2.4.1、全空間比較の射の構成。 -/
lemma relativeJoinCylinder_extension_exists {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (u : pushout (prismEndpoint 1 X) f ⟶ E) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E, relativeJoinCylinderComparison f ≫ G = u := by
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective (relativeJoinCylinderComparison f)
    (isPrecompositionEquivalence_relativeJoinCylinderComparison f E).choose.isEssentiallySurjective
    (functorVertex u)
  obtain ⟨G, rfl⟩ := (functorVertexEquiv _ _).surjective v
  refine ⟨G, ?_⟩
  apply functorVertex_injective
  exact hv

/-- 概要：prism と終域上に与えた整合する二射を relative join 全体へ延長できる。
方針：二射を写像円柱からの射に貼り、比較に沿う延長を取る。
規約：終端の一致条件を厳密な等式で指定する。
使われ方：Kerodon Theorem 5.2.4.1、区間上の比較の全体の射。 -/
lemma relativeJoin_extension_of_prism {X Y E : SSet.{u}}
    (f : X ⟶ Y) [Mono f] [Quasicategory E]
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) :
    ∃ G : relativeJoin f (𝟙 Y) ⟶ E,
      relativeJoinPrism f ≫ G = H ∧ relativeJoinInr f (𝟙 Y) ≫ G = g := by
  obtain ⟨G, hG⟩ := relativeJoinCylinder_extension_exists f (pushout.desc H g w)
  refine ⟨G, ?_, ?_⟩
  · have he := congrArg (fun q ↦ pushout.inl (prismEndpoint 1 X) f ≫ q) hG
    simpa only [← Category.assoc, relativeJoinCylinderComparison_inl, pushout.inl_desc] using he
  · have he := congrArg (fun q ↦ pushout.inr (prismEndpoint 1 X) f ≫ q) hG
    simpa only [← Category.assoc, relativeJoinCylinderComparison_inr, pushout.inr_desc] using he

end SerrePositivity.InfinityCategories
