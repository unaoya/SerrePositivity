module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.JointComparisonComposition
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：指定 straightening 底変換同型を初頂点へ戻して元の共同切断比較を回収する。
方針：局所化前合成の充満忠実性で選んだ同型の像を計算する。
規約：指定された降下同型と指定された切断比較を保持する。
使われ方：P-12 の反復底変換の合成則を降下前の共同比較へ還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：底変換前後の初頂点制限の始点を同じ共同図式として同定する。
方針：初頂点写像の指定自然性を宇宙変更後に用いる。
規約：元の底写像を保持する。使われ方：降下前の比較の始点の正規化。 -/
lemma straighteningBaseChange_firstVertex_source {B D : SSet.{u}} (k : D ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B) =
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
  rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]

/-- 概要：元の共同切断底変換比較を、降下した二図式の初頂点制限の同型として表示する。
方針：二つの指定制限同型の間へ元の切断比較の逆を置く。
規約：同型を選び直さない。使われ方：指定降下同型の制限の回収。 -/
def straighteningBaseChangeRestrictionIso {B D : SSet.{u}} (k : D ⟶ B) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B))
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
        (leftStraighteningSectionJointDiagram D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) :=
  eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
      (straighteningBaseChange_firstVertex_source k)) ≪≫
    (leftStraighteningSectionJointDiagram_restrictIso B).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
    (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
    ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp
      ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})).symm

/-- 概要：指定関手同型の前合成は、内部前合成の同じ頂点同型の像。
方針：前合成の元の定義で、端点の定義的等式を消去する。
規約：元の同型を保持する。使われ方：大きい指定同型を展開しない制限計算。 -/
lemma functorIsoPrecomp_heq_map {W X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (q : W ⟶ X) :
    HEq (e.precomp q) (VertexIso.map e ((pre q).app Y)) := by
  rfl

/-- 概要：元の指定底変換同型は、元の共同切断比較の指定した充満忠実逆像。
方針：降下同型と制限同型の定義を一度だけ照合する。
規約：別の逆像を選ばない。使われ方：同型の大きい定義を制限計算から分離する。 -/
lemma straighteningBaseChangeIso_eq_preimage {B D : SSet.{u}} (k : D ⟶ B) :
    leftStraighteningSectionJointDiagram_baseChangeIso k =
      (localization_pre_isFullyFaithful
        (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} D)
        ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u})).preimageVertexIso
          (straighteningBaseChangeRestrictionIso k) := by
  rfl

/-- 概要：指定降下同型の初頂点制限は元の共同切断比較を厳密に回収する。
方針：指定された充満忠実前合成の逆像の像を使う。
規約：対象ごとの存在に弱めず、元の同型そのものを比較する。
使われ方：底変換同型の合成の照合を共同切断図式へ降ろす。 -/
lemma straighteningBaseChangeIso_firstVertex {B D : SSet.{u}} (k : D ⟶ B) :
    (leftStraighteningSectionJointDiagram_baseChangeIso k).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)) =
      straighteningBaseChangeRestrictionIso k := by
  let L := (pre ((SSet.uliftFunctor.{u + 1, u}).map
    (transportSimplexFirstVertexMap D))).app
      ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u})
  have h₁ := congrArg (fun e ↦ VertexIso.map e L) (straighteningBaseChangeIso_eq_preimage k)
  have h₂ := (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} D)
    ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u})).preimageVertexIso_map
      (x := functorVertex ((SSet.uliftFunctor.{u + 1, u}).map k ≫
        leftStraighteningSectionJointDiagram B))
      (y := functorVertex (leftStraighteningSectionJointDiagram D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))
      (straighteningBaseChangeRestrictionIso k)
  exact eq_of_heq ((functorIsoPrecomp_heq_map
    (leftStraighteningSectionJointDiagram_baseChangeIso k)
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D))).trans
      (h₁.trans h₂).heq)

/-- 概要：充満忠実な内部前合成は、指定した関手同型の等式を反映する。
方針：前合成を頂点同型の像へ戻し、ホモトピー圏の忠実性を使う。
規約：同型の存在でなく等式を反映する。使われ方：指定底変換合成則の降下。 -/
lemma functorIso_precomp_injective {W X Y : SSet.{u}} [Quasicategory Y]
    (q : W ⟶ X) (hq : IsFullyFaithful ((pre q).app Y))
    {f g : X ⟶ Y} (e e' : FunctorIso f g) (h : e.precomp q = e'.precomp q) : e = e' := by
  have hm : VertexIso.map e ((pre q).app Y) = VertexIso.map e' ((pre q).app Y) :=
    eq_of_heq ((functorIsoPrecomp_heq_map e q).symm.trans
      (h.heq.trans (functorIsoPrecomp_heq_map e' q)))
  apply Iso.ext
  apply hq.toHoFullyFaithful.map_injective
  exact congrArg Iso.hom hm

end SerrePositivity.InfinityCategories.F2.Presentable
