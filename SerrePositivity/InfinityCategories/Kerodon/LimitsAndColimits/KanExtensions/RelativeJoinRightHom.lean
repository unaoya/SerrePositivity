module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingCylinderHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderEquivalence
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：相対 join の図式から底に沿う図式への射の右端での表示。
方針：円柱比較の充満忠実性で移し、円柱の右端への Hom 全単射を使う。
規約：元の図式に局所余極限性を要求しない。
使われ方：左端への制限の全単射と合成して Kan 拡張の Hom 公式へ進む。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：等しい両端の関手の間で h Fun の Hom を輸送する。
方針：両端の等式の同型による Hom の共役を使う。
規約：輸送の前後の関手を明示する。
使われ方：円柱比較が保つ底射影と右包含の厳密な等式の利用。 -/
def kanFunctorHomCongr {A D : SSet.{u}} {U V U' V' : A ⟶ D}
    (hU : U = U') (hV : V = V') : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' V' :=
  Iso.homCongr (eqToIso (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hU))
    (eqToIso (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hV))

/-- 概要：円柱比較による制限は底射影に沿う標的への Hom の全単射。
方針：円柱比較の前合成同値の充満忠実性と底射影の一致を使う。
規約：quasicategory 性は標的 D のみ。
使われ方：相対 join の右端の Hom 対応への第一段階。 -/
def kanRelativeJoinCylinderHomEquiv {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison p D).isFullyFaithful
      |>.toHoFullyFaithful.homEquiv).trans
    (kanFunctorHomCongr (U := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ H)
      (V := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G))
      rfl (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_baseProjection]))

/-- 概要：相対 join の底射影に沿う標的への Hom は右端への制限上の Hom と同値。
方針：円柱比較の Hom 全単射、円柱の随伴、右包含の一致を合成する。
規約：構造射 p には cocartesian 性も quasicategory 性も要求しない。
使われ方：普遍な相対 join 図式の左端への制限と合成する右端の対応。 -/
def kanRelativeJoinRightHomEquiv {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H) G :=
  (kanRelativeJoinCylinderHomEquiv p H G).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderHomEquiv p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ H) G).trans
      (kanFunctorHomCongr (by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr]) rfl))

/-- 概要：右端の Hom 全単射は、右包含による前合成そのもので与えられる。
方針：円柱の公式を展開し、二重の制限を右包含の前合成へ同定する。
規約：標的の底射影の同一視だけを端点の等式で補う。
使われ方：点ごとの Kan 条件から指定変換の大域的 Hom 公式への接続。 -/
lemma kanRelativeJoinRightHomEquiv_apply {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) (G : C ⟶ D)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G)) :
    kanRelativeJoinRightHomEquiv p H G α =
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C))).app D)).toFunctor.map α ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q))
          (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G) = G by
            rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_baseProjection, Category.id_comp])) := by
  have hp : (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p)).app D ≫
      (pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D =
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C))).app D := by
    rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr]
  have hp' : (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p)).app D)).toFunctor ⋙
      (hoFunctor.map ((pre (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p)).app D)).toFunctor =
        (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C))).app D)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp, hp]
  have hh := CategoryTheory.Functor.congr_hom hp' α
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection p ≫ G := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_baseProjection]
  have hi : pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr]
  change eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hi).symm ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderHomEquiv p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p ≫ H) G
      (𝟙 _ ≫ (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison p)).app D)).toFunctor.map α ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) hq)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingCylinderHomEquiv_apply]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc]
  erw [hh]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  simp only [Category.assoc, eqToHom_trans]

/-- 概要：右端の Hom 全単射は底上の関手間の射による後合成に自然。
方針：右包含と底射影の合成の恒等式を自然な余単位とし、その自然性を使う。
規約：射 τ は h Fun の任意の射。
使われ方：右端の対応の逆を単位との合成で表す。 -/
lemma kanRelativeJoinRightHomEquiv_comp {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) {G G' : C ⟶ D}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ G)) (τ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G') :
    kanRelativeJoinRightHomEquiv p H G'
        (α ≫ (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))).app D)).toFunctor.map τ) =
      kanRelativeJoinRightHomEquiv p H G α ≫ τ := by
  have hr :
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))).app D)).toFunctor ⋙
        (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C))).app D)).toFunctor = 𝟭 _ := by
    rw [← Cat.Hom.comp_toFunctor, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_baseProjection, pre_id,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Cat.Hom.id_toFunctor]
  have h := (eqToHom hr).naturality τ
  simp only [eqToHom_app] at h
  rw [kanRelativeJoinRightHomEquiv_apply, kanRelativeJoinRightHomEquiv_apply,
    CategoryTheory.Functor.map_comp, Category.assoc]
  erw [h]
  rw [Category.assoc]
  rfl

/-- 概要：相対 join の右端の恒等射に対応する大域的な単位。
方針：右端の Hom 全単射の逆像を取る。
規約：元の指定 Kan 変換との同定はまだ含まない。
使われ方：右端への対応の逆の合成公式。 -/
def kanRelativeJoinUnitHom {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H)) :=
  (kanRelativeJoinRightHomEquiv p H (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H)).symm (𝟙 _)

/-- 概要：右端の Hom 対応の逆は単位と底射影に沿う前合成の合成。
方針：右端の全単射の単射性で比較し、その後合成自然性を使う。
規約：任意の h Fun の射を扱う。
使われ方：左端への制限後の Kan 変換の Hom 公式。 -/
lemma kanRelativeJoinRightHomEquiv_symm_apply {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) ⟶ D) (G : C ⟶ D)
    (τ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) ≫ H) G) :
    (kanRelativeJoinRightHomEquiv p H G).symm τ =
      kanRelativeJoinUnitHom p H ≫
        (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))).app D)).toFunctor.map τ := by
  apply (kanRelativeJoinRightHomEquiv p H G).injective
  rw [Equiv.apply_symm_apply, kanRelativeJoinRightHomEquiv_comp]
  simp only [kanRelativeJoinUnitHom, Equiv.apply_symm_apply, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
