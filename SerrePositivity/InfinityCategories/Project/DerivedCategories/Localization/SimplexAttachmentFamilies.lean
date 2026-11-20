module


public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.SimplexAttachmentBoundary

/-!
概要：前段の全比較と次辺の全比較を、共有点を厳密に保って同時に貼る。
方針：実 pushout の内部 Hom による pullback と、inner anodyne 制限の全単射 RLP を使う。
規約：任意のパラメータ族と指定部分族を保持し、ホモトピー圏の等式だけに落とさない。
使われ方：c5 の全有限図式の商比較における prism の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 前段と次辺の全族を、元の共有点に沿って一つの境界族へ貼る。 -/
def simplexAttachmentFamilyGlue {P X : SSet.{u}} (n : ℕ)
    (a : P ⟶ (ihom (Δ[n] : SSet.{u})).obj X)
    (b : P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj X)
    (hab : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app X =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app X) :
    P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u})).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).lift a b hab

@[reassoc]
lemma simplexAttachmentFamilyGlue_prefix {P X : SSet.{u}} (n : ℕ)
    (a : P ⟶ (ihom (Δ[n] : SSet.{u})).obj X)
    (b : P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj X)
    (hab : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app X =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue n a b hab ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X = a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).lift_fst a b hab

@[reassoc]
lemma simplexAttachmentFamilyGlue_lastEdge {P X : SSet.{u}} (n : ℕ)
    (a : P ⟶ (ihom (Δ[n] : SSet.{u})).obj X)
    (b : P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj X)
    (hab : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app X =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue n a b hab ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X = b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).lift_snd a b hab

/-- 指定部分族と、前段・次辺・共有点の全族を同時に保持する実全図式の延長。 -/
lemma exists_relative_simplexAttachmentFamily {P Q X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (i : P ⟶ Q) [Mono i]
    (f : P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (a : Q ⟶ (ihom (Δ[n] : SSet.{u})).obj X)
    (b : Q ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj X)
    (hab : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app X =
      b ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app X)
    (ha : i ≫ a = f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X)
    (hb : i ≫ b = f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X) :
    ∃ L : Q ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X,
      i ≫ L = f ∧ L ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X = a ∧
        L ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app X = b := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue n a b hab
  have hT : i ≫ T = f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app X := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary_isPushout n) X).hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_prefix]
      simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix_ι] using ha
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_lastEdge]
      simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge_ι] using hb
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app X) i inferInstance
  let sq : CommSq f i ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app X) T := ⟨hT.symm⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have he := congrArg (· ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n)).app X) sq.fac_right
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_prefix] at he
    simpa only [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix_ι] using he
  · have he := congrArg (· ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n)).app X) sq.fac_right
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentFamilyGlue_lastEdge] at he
    simpa only [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge_ι] using he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
