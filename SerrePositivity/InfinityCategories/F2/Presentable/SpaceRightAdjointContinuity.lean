module

public import SerrePositivity.InfinityCategories.F2.Presentable.AdjunctionHomPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeSpaceUniverseReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.SpaceUniverseLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallConstantDiagramCompact
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor

/-!
概要：空間値の右随伴の指定濃度の filtered 保存を、左随伴による一点の像の compact 性で判定する。
方針：随伴の全 Hom 同型と、一点からの Hom の宇宙変更比較を使って元の保存性を反映する。
規約：元の指定濃度を変更せず、一般の右随伴の accessibility だけで代用しない。
使われ方：μ-small な極限関手の μ-filtered 余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：空間値の右随伴は、左随伴の一点の像が μ-compact なら μ-filtered 余極限を保つ。
方針：随伴 Hom の保存を一点 Hom と宇宙変更の全自然同型で読み替え、元の全余錐で反映する。
規約：始域の accessibility や元の右随伴の保存性を要求しない。
使われ方：小さい極限関手の濃度を指定した保存判定。 -/
lemma spaceRightAdjoint_isKappaAccessibleFunctor_of_point_compact
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    {L : SpaceInfinity.{u} ⟶ C} {R : C ⟶ SpaceInfinity.{u}} (a : QCatAdjunction L R)
    (hL : Compact.IsKappaCompact.{u, u + 1} μ
      (L.app (Opposite.op ⦋0⦌) (coherentNerveVertex pointKanObject.{u}))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ R := by
  have h := (adjunction_hom_preservesKappaFilteredColimits_iff a μ
    (coherentNerveVertex pointKanObject.{u})).mpr hL
  apply isKappaAccessibleFunctor_of_spaceUniverse_image
  exact h.of_functorIso
    (spaceUniverse_covariantPointIso.precomp ((SSet.uliftFunctor.{u + 2, u + 1}).map R))

/-- 概要：μ-small な形状上の定値図式関手の右随伴は、指定した μ-filtered 余極限を保つ。
方針：一点定値図式の compact 性を空間値右随伴の一点判定へ渡す。
規約：形状は小さい quasicategory、μ は非可算正則とする。
使われ方：一般 coherent な小さい極限と filtered 余極限の交換への入口。 -/
lemma constantFunctor_rightAdjoint_isKappaAccessibleFunctor
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (B : SSet.{u}) [Quasicategory B] (hB : IsKappaSmall μ B)
    {R : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶ SpaceInfinity.{u}}
    (a : QCatAdjunction (constantFunctorMap ((SSet.uliftFunctor.{u + 1, u}).obj B)
      SpaceInfinity.{u}) R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ R := by
  apply spaceRightAdjoint_isKappaAccessibleFunctor_of_point_compact a
  rw [constantFunctorMap_vertex]
  exact smallConstantPointDiagram_isKappaCompact hμ B hB

end SerrePositivity.InfinityCategories.F2.Presentable
