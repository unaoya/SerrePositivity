module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientNaturality

/-!
概要：底の単体上の係数評価を、重み付き図式の最後の成分の輸送として計算する。
方針：底変換の持ち上げを明示的な単体で一意に同定し、終対象評価を計算する。
規約：底の単調写像は最後の頂点を保つとは限らない。
使われ方：Kerodon §5.3.3（Tag 025W）、係数充填と元のホーンの全ての面の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：weighted nerve の単体の終対象評価は最後の成分に終対象への輸送を続けた射。
方針：Yoneda の後合成の式で、定義した係数の自然変換と評価を計算する。
規約：底の圏と係数の充填性は要求しない。
使われ方：Kerodon §5.3.3（Tag 025W）、底の標準単体上の係数評価の計算則。 -/
lemma weightedNerveTerminalEvaluation_yoneda {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) :
    SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation F ht =
      s.2.app (Fin.last n) ≫ F.map (ht.from (s.1.obj (Fin.last n))) := by
  rw [SSet.yonedaEquiv_symm_comp]
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv
    (s.2.app (Fin.last n) ≫ F.map (ht.from (s.1.obj (Fin.last n))))) = _
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- 概要：単調写像を持ち上げた有限順序集合への射列にする。
方針：単調写像の順序関手に ULift の逆順序同型を続ける。
規約：元の単調写像の標的の有限順序集合を宇宙 u に持ち上げる。
使われ方：Kerodon §5.3.3（Tag 025W）、底変換した weighted nerve の単体の明示表示。 -/
def weightedNerveSimplexIndexChain {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + 1) ⥤ ULift.{u} (Fin (n + 1)) :=
  (SimplexCategory.toCat.map α).toFunctor ⋙
    (ULift.orderIso : ULift.{u} (Fin (n + 1)) ≃o Fin (n + 1)).symm.monotone.functor

/-- 概要：持ち上げた射列の nerve の単体は標準単体の単調写像を表す。
方針：各次数で有限順序集合の頂点の値を計算する。
規約：標準単体と持ち上げた有限順序集合の nerve の同型を使う。
使われ方：Kerodon §5.3.3（Tag 025W）、明示的な係数単体の底の確認。 -/
lemma weightedNerveSimplexIndexChain_projection {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (stdSimplex.map α : (Δ[m] : SSet.{u}) ⟶ Δ[n]) ≫ (stdSimplex.isoNerve.{u} n).hom =
      SSet.yonedaEquiv.symm (weightedNerveSimplexIndexChain.{u} α) := by
  apply SSet.hom_ext
  rintro ⟨⟨l⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：指定した底の部分単体上の係数評価は最後の成分の輸送に一致する。
方針：底変換の pullback の持ち上げを明示し、終対象への評価の Yoneda の式を使う。
規約：h は相対図式の可換性であり、その証明の選択は結果に影響しない。
使われ方：Kerodon §5.3.3（Tag 025W）、係数ホーンの各面を元の重み付き図式と比較する主計算。 -/
lemma weightedNerveSimplexCoefficient_diagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {m n : ℕ} (σ : ComposableArrows C n) (α : ⦋m⦌ ⟶ ⦋n⦌)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight m ⟶ (SimplexCategory.toCat.map α).toFunctor ⋙ σ ⋙ F)
    (h : SSet.yonedaEquiv.symm
        (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = stdSimplex.map α ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ
        (SSet.yonedaEquiv.symm
          (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m))
        (stdSimplex.map α) h =
      τ.app (Fin.last m) ≫ F.map (σ.map
        (homOfLE (Fin.le_last (α.toOrderHom (Fin.last m))))) := by
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex (I ⋙ F) m := ⟨weightedNerveSimplexIndexChain α, τ⟩
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient
  have hb : SSet.yonedaEquiv.symm
      (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (stdSimplex.map α ≫ (stdSimplex.isoNerve.{u} n).hom) ≫ nerveMap I := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor_projection]
    exact h
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift I F
      (SSet.yonedaEquiv.symm
        (⟨(SimplexCategory.toCat.map α).toFunctor ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F m))
      (stdSimplex.map α ≫ (stdSimplex.isoNerve.{u} n).hom) hb = SSet.yonedaEquiv.symm s := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap_isPullback I F).hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base, SSet.yonedaEquiv_symm_comp]
      rfl
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_projection, SSet.yonedaEquiv_symm_comp]
      exact weightedNerveSimplexIndexChain_projection α
  rw [he, weightedNerveTerminalEvaluation_yoneda]
  change τ.app (Fin.last m) ≫ F.map (σ.map _) = _
  exact congrArg (fun q ↦ τ.app (Fin.last m) ≫ F.map (σ.map q)) (Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
