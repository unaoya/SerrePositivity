module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementConstant
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementBaseChange

/-!
概要：定値係数からの自然変換による simplicial replacement の組み立てと底変換。
方針：定値図式の直積表示に係数の自然変換を適用し、底変換の四角形を各次数で計算する。
規約：始対象の存在は要求せず、係数の自然変換をデータとして指定する。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、有限順序の末尾と最初の係数部分の貼り合わせ。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：定値係数の自然変換が底の nerve と係数の直積からの射を定める。
方針：定値図式の直積同型の逆を係数変換の全空間の射へ合成する。
規約：F の Kan 性は要求しない。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、最初の係数部分の末尾への制限。 -/
def simplicialReplacementAssembly {C : Type u} [Category.{u} C]
    {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    nerve C ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantIso C K).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap η

/-- 概要：定値係数による組み立て射は通常の関手による底変換と可換。
方針：底の射列への後合成と始点での係数変換の式を計算する。
規約：係数 K は変えず、図式と自然変換を H で制限する。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、最初の係数部分と末尾部分の可換な貼り合わせ。 -/
lemma simplicialReplacementAssembly_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft H η) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap H F =
      (nerveMap H ▷ K) ≫ simplicialReplacementAssembly η := rfl

/-- 概要：組み立て射と底変換の比較四角形は pullback。
方針：各次数で底の射列と定値係数の単体を取り出し、可換な対を一意に戻す。
規約：底の関手の単射性や自然変換の単射性は不要。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、末尾部分との交わりの厳密な表示。 -/
lemma simplicialReplacementAssembly_baseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {K : SSet.{u}} {F : C ⥤ SSet.{u}}
    (η : (CategoryTheory.Functor.const C).obj K ⟶ F) :
    IsPullback (simplicialReplacementAssembly (CategoryTheory.Functor.whiskerLeft H η))
      (nerveMap H ▷ K) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap H F)
      (simplicialReplacementAssembly η) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
    have hσ : σ = σ' := congrArg Sigma.fst h.1
    have hs : s = s' := congrArg Prod.snd h.2
    exact Prod.ext hσ hs
  · rintro ⟨σ, τ⟩ ⟨δ, s⟩ h
    have hσ : σ ⋙ H = δ := congrArg Sigma.fst h
    subst δ
    refine ⟨(σ, s), ?_, rfl⟩
    refine Sigma.ext (by rfl) ?_
    exact (Sigma.mk.inj h).2.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
