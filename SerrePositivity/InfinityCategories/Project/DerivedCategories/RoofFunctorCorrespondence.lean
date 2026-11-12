module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.RoofTargetFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberBaseChange

/-! # 関手による実屋根の変換と固定 Hom の自然性

概要：始域図式と可換な任意の関手を、実屋根全体の写像へ持ち上げる。
方針：標的 slice の関手性と pullback の普遍性を使う。
規約：全次数の厳密な等式。使われ方：反転関手の屋根評価と高次の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 始域図式を保つ関手による、実屋根の全空間の変換。 -/
def roofFunctorMap {I X Y : SSet.{u}} (s : I ⟶ X) (t : I ⟶ Y)
    (F : X ⟶ Y) (h : s ≫ F = t) (y : X _⦋0⦌) :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) s ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) y))) t :=
  pullback.lift (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F y) (pullback.snd _ _) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_projection, ← Category.assoc,
      pullback.condition, Category.assoc, h])

/-- 屋根の関手写像の標的 slice 成分。 -/
lemma roofFunctorMap_fst {I X Y : SSet.{u}} (s : I ⟶ X) (t : I ⟶ Y)
    (F : X ⟶ Y) (h : s ≫ F = t) (y : X _⦋0⦌) :
    roofFunctorMap s t F h y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F y :=
  pullback.lift_fst _ _ _

/-- 屋根の関手写像は実添字を厳密に固定する。 -/
lemma roofFunctorMap_snd {I X Y : SSet.{u}} (s : I ⟶ X) (t : I ⟶ Y)
    (F : X ⟶ Y) (h : s ≫ F = t) (y : X _⦋0⦌) :
    roofFunctorMap s t F h y ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- 恒等関手による屋根変換は厳密な恒等射。 -/
lemma roofFunctorMap_id {I X : SSet.{u}} (s : I ⟶ X) (y : X _⦋0⦌) :
    roofFunctorMap s s (𝟙 X) (Category.comp_id s) y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [roofFunctorMap_fst, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_id, Category.comp_id, Category.id_comp]
    rfl
  · rw [roofFunctorMap_snd, Category.id_comp]
    rfl

/-- 屋根変換は関手の合成を全高次単体で保つ。 -/
lemma roofFunctorMap_comp {I X Y Z : SSet.{u}} (s : I ⟶ X) (t : I ⟶ Y)
    (r : I ⟶ Z) (F : X ⟶ Y) (G : Y ⟶ Z)
    (hF : s ≫ F = t) (hG : t ≫ G = r) (y : X _⦋0⦌) :
    roofFunctorMap s t F hF y ≫ roofFunctorMap t r G hG
      (F.app (Opposite.op ⦋0⦌) y) =
    roofFunctorMap s r (F ≫ G) (by rw [← Category.assoc, hF, hG]) y := by
  apply pullback.hom_ext
  · have hf := roofFunctorMap_fst s r (F ≫ G)
      (by rw [← Category.assoc, hF, hG]) y
    simp only [NatTrans.comp_app, types_comp_apply] at hf
    rw [hf, Category.assoc, roofFunctorMap_fst, ← Category.assoc, roofFunctorMap_fst,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_comp]
  · have hs := roofFunctorMap_snd s r (F ≫ G)
      (by rw [← Category.assoc, hF, hG]) y
    simp only [NatTrans.comp_app, types_comp_apply] at hs
    rw [hs, Category.assoc, roofFunctorMap_snd, roofFunctorMap_snd]

/-- 指定添字の固定 Hom を、その添字 fiber として屋根全体へ含める。 -/
def roofFixedHomInclusion {I X : SSet.{u}} (s : I ⟶ X)
    (a : I _⦋0⦌) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (s.app (Opposite.op ⦋0⦌) a) y ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) s :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso _ _).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso _ s a).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd _ s) a

/-- 固定 Hom の屋根への包含の標的 slice 成分。 -/
lemma roofFixedHomInclusion_fst {I X : SSet.{u}} (s : I ⟶ X)
    (a : I _⦋0⦌) (y : X _⦋0⦌) :
    roofFixedHomInclusion s a y ≫ pullback.fst _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso _ _).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y))
          (s.app (Opposite.op ⦋0⦌) a) := by
  dsimp only [roofFixedHomInclusion]
  rw [Category.assoc, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso_hom_ι,
    Iso.inv_hom_id_assoc]

/-- 固定 Hom の屋根への包含は添字 a 上にある。 -/
lemma roofFixedHomInclusion_snd {I X : SSet.{u}} (s : I ⟶ X)
    (a : I _⦋0⦌) (y : X _⦋0⦌) :
    roofFixedHomInclusion s a y ≫ pullback.snd _ _ = SSet.const a := by
  dsimp only [roofFixedHomInclusion]
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 屋根の関手変換と固定 Hom 上の作用は厳密に可換。 -/
lemma roofFunctorMap_fixedHom {I X Y : SSet.{u}} (s : I ⟶ X) (F : X ⟶ Y)
    (a : I _⦋0⦌) (y : X _⦋0⦌) :
    roofFixedHomInclusion s a y ≫ roofFunctorMap s (s ≫ F) F rfl y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (s.app (Opposite.op ⦋0⦌) a) y ≫
        roofFixedHomInclusion (s ≫ F) a (F.app (Opposite.op ⦋0⦌) y) := by
  apply pullback.hom_ext
  · rw [Category.assoc, roofFunctorMap_fst, ← Category.assoc,
      roofFixedHomInclusion_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_pinched,
      Category.assoc, roofFixedHomInclusion_fst]
    rfl
  · rw [Category.assoc, roofFunctorMap_snd, roofFixedHomInclusion_snd,
      Category.assoc, roofFixedHomInclusion_snd, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
