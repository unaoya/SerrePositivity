module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FiberwiseFunctorDescent

/-!
概要：fiber ごとの関手の族と、元の底上の図式の全単射。
方針：全単体の余極限から降ろした図式の各成分を計算し、curry との往復を示す。
規約：F が全単体の通常の余極限を保つことだけを仮定する。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR） の大域的な持ち上げ問題を族の持ち上げ問題へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：回収した全空間上の図式から族を作ると元の族になる。
方針：各単体への制限を余極限の計算則と成分の回収の等式で照合する。
規約：元の底の射も厳密に保つ。
使われ方：全単射の一方の往復。 -/
lemma fiberwiseFunctorCurry_uncurry {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) [PreservesColimitsOfShape A.Elementsᵒᵖ F] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry F
      ⟨f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorUncurry F f⟩ = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change (⟨SSet.yonedaEquiv.symm x ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D),
      F.map (Over.homMk (SSet.yonedaEquiv.symm x) rfl :
        Over.mk (SSet.yonedaEquiv.symm x ≫ (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ⟶
          Over.mk (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorUncurry F f⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D (stdSimplex.obj n.unop)) = f.app n x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorUncurry_fac]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorComponent_pair F f (SSet.yonedaEquiv.symm x)).trans
    ((SSet.yonedaEquiv_comp (SSet.yonedaEquiv.symm x) f).trans
      (congrArg (fun q ↦ f.app n q) (SSet.yonedaEquiv.apply_symm_apply x)))

/-- 概要：全単体の余極限を保つ F では族への構成は単射。
方針：射影で底の等式を得て、各単体での成分の一致を余極限から大域的な一致にする。
規約：底の異なる図式も含む依存和全体での単射性。
使われ方：往復と大域的な図式の一意性の検証。 -/
lemma fiberwiseFunctorCurry_injective {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    [PreservesColimitsOfShape A.Elementsᵒᵖ F] :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (A := A) (D := D) F) := by
  intro s t h
  have hb : s.1 = t.1 := by
    have he := congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry_projection] using he
  rcases s with ⟨a, s⟩
  rcases t with ⟨b, t⟩
  dsimp only at hb
  subst b
  suffices hs : s = t by
    cases hs
    rfl
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.simplexCocone_map_isColimit F a).hom_ext
  intro j
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app h j.unop.obj) j.unop.val
  exact eq_of_heq (Sigma.mk.inj he).2

/-- 概要：底上の実際の図式と fiber ごとの関手の族の全単射。
方針：curry と全単体の余極限による uncurry を往復させる。
規約：これは単体集合への射全体の普遍性であり、π₀ の対応ではない。
使われ方：族を用いた大域的な Kan 拡張の組み立て。 -/
def fiberwiseFunctorHomEquiv {B A D : SSet.{u}} (F : Over B ⥤ SSet.{u})
    [PreservesColimitsOfShape A.Elementsᵒᵖ F] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D A ≃ (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor F D) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry F
  invFun f := ⟨f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection F D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorUncurry F f⟩
  left_inv _s := fiberwiseFunctorCurry_injective F (fiberwiseFunctorCurry_uncurry F _)
  right_inv f := fiberwiseFunctorCurry_uncurry F f

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
