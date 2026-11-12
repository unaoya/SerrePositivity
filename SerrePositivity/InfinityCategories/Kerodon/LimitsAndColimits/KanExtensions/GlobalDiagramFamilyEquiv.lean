module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalDiagramFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomLiftingEquiv

/-!
概要：全空間上の図式と恒等射上の fiber ごとの関手の族との全単射。
方針：相対指数の普遍性と、恒等射に沿う pullback の第二射影の同型を合成する。
規約：全ての単体集合を任意とする。
使われ方：普遍余錐の coherent な族を実際の相対 join 上の図式へ戻す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：全空間上の図式と恒等射上の族は全単射。
方針：第二射影の逆で図式を戻し、pullback 上の curry と uncurry を使う。
規約：射影を恒等射に等号で固定する。
使われ方：coherent な余錐の選択を実際の図式として回収する。 -/
def kanGlobalDiagramFamilyEquiv {K C D : SSet.{u}} (p : K ⟶ C) :
    (K ⟶ D) ≃ {b : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D // b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D = 𝟙 C} where
  toFun F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily p F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily_projection p F⟩
  invFun b := inv (pullback.snd (𝟙 C) p) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (𝟙 C)).symm b
  left_inv F := by
    change inv (pullback.snd (𝟙 C) p) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (𝟙 C)).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (𝟙 C)) (pullback.snd (𝟙 C) p ≫ F)) = F
    rw [Equiv.symm_apply_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  right_inv b := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (𝟙 C)
      (pullback.snd (𝟙 C) p ≫ inv (pullback.snd (𝟙 C) p) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (𝟙 C)).symm b) = b.val
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (𝟙 C)).apply_symm_apply b)

/-- 概要：全空間上の図式の族への対応は単射。
方針：全単射の単射性を使う。
規約：底の恒等射の等式は証明無関係性で消す。
使われ方：族の制限の等式を図式の制限の等式へ戻す。 -/
lemma kanGlobalDiagramFamily_injective {K C D : SSet.{u}} (p : K ⟶ C) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily (D := D) p) := by
  intro F G h
  exact (kanGlobalDiagramFamilyEquiv p).injective (Subtype.ext h)

/-- 概要：全空間の図式の族への対応は底上の図式の制限と可換。
方針：curry の制限の自然性と pullback の第二射影の可換性を使う。
規約：制限の向きは底上の対象の射と逆。
使われ方：相対 join の左端への制限を元の図式として回収する。 -/
lemma kanGlobalDiagramFamily_pre {C D : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (F : L.left ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily L.hom F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily K.hom (i.left ≫ F) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanGlobalDiagramFamily
  erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre i]
  congr 1
  rw [← Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_snd]
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
