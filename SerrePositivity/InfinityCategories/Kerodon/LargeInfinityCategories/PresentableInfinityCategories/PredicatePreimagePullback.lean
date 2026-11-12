module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexPullbackRestriction

/-!
概要：頂点条件の逆像による全部分圏を、元の射に沿う厳密な引き戻しと比較する。
方針：全部分包含と条件付き射影を引き戻しに束ね、その逆を同じ頂点条件から作る。
規約：全単体の同型であり、quasicategory 性を要求しない。
使われ方：compact 始域を持つ slice の射影と fiber の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：頂点条件の逆像への射の制限。
方針：全部分包含の後の元の射を同じ条件へ持ち上げる。
規約：元の全射を保持する。
使われ方：条件付き slice の始域射影。 -/
def predicatePreimageMap {E B : SSet.{u}} (p : E ⟶ B) (P : B _⦋0⦌ → Prop) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (fun x ↦ P (p.app _ x)) : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (fun x ↦ P (p.app _ x))).ι ≫ p)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x)

/-- 概要：頂点条件の逆像は元の全部分包含の実引き戻しと同型。
方針：二射影を全頂点条件で持ち上げ、包含の単射性で往復を示す。
規約：全単体の厳密な同型。
使われ方：条件付き slice の充填性と小さい fiber の移送。 -/
def predicatePreimagePullbackIso {E B : SSet.{u}} (p : E ⟶ B)
    (P : B _⦋0⦌ → Prop) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (fun x ↦ P (p.app _ x)) : SSet.{u}) ≅
      pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι := by
  let Q := fun x ↦ P (p.app _ x)
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E Q).ι
  let k := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι
  let f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E Q : SSet.{u}) ⟶ pullback p k :=
    pullback.lift j (predicatePreimageMap p P) (by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P _ _).symm)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift Q (pullback.fst p k) (fun x ↦ by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (pullback.condition (f := p) (g := k)) (Opposite.op ⦋0⦌)) x
    change p.app _ ((pullback.fst p k).app _ x) =
      ((pullback.snd p k).app _ x).val at h
    change P (p.app _ ((pullback.fst p k).app _ x))
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((pullback.snd p k).app _ x))
  refine ⟨f, g, ?_, ?_⟩
  · apply (cancel_mono j).mp
    change (f ≫ g) ≫ j = (𝟙 _) ≫ j
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · change (g ≫ f) ≫ pullback.fst p k = (𝟙 _) ≫ pullback.fst p k
      rw [Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, Category.id_comp]
    · apply (cancel_mono k).mp
      change ((g ≫ f) ≫ pullback.snd p k) ≫ k = _
      dsimp only [f, g, j, k]
      simp only [Category.assoc, pullback.lift_snd, predicatePreimageMap,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, Category.id_comp]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, pullback.condition]

/-- 概要：頂点条件による逆像の正方形は実引き戻し。
方針：二射影を厳密に保つ構成済み同型を使う。
規約：任意の頂点条件と全単体で成立する。
使われ方：条件付き射影の fibration 性と fiber 同型。 -/
lemma predicatePreimage_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    (P : B _⦋0⦌ → Prop) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (fun x ↦ P (p.app _ x))).ι
      (predicatePreimageMap p P) p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B P).ι := by
  apply IsPullback.of_iso_pullback
    (CommSq.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P _ _).symm)
    (predicatePreimagePullbackIso p P)
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
