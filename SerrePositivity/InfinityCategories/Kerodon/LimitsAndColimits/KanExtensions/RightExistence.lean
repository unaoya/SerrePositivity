module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.TransportOppositeUniversality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeInvolution

/-!
概要：標準局所図式の極限の存在から右 Kan 拡張を構成する。
方針：左の存在定理と指定変換を保つ双対化を使い、二重反転を厳密に消去する。
規約：K・C・D は同じ宇宙の quasicategory、δ は任意。
使われ方：Kerodon §7.3.5（Tag 02ZZ） の左右 Kan 拡張の点ごとの存在の判定。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：反転した局所図式の極限から反転した関手に沿う右 Kan 拡張を作る。
方針：局所余極限へ戻して左拡張を構成し、指定変換とその Kan 条件を反転する。
規約：構成した関手と指定変換の両方を返す。
使われ方：一般の右 Kan 拡張の存在定理の双対化の段階。 -/
lemma exists_kanRightExtension_op_of_local_limits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hlim : ∀ c : C.op _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀) c)) :
    ∃ (F : C.op ⟶ D.op)
      (α : SSet.Homotopy (SSet.opFunctor.map δ ≫ F) (SSet.opFunctor.map F₀)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀) F α := by
  have hcol : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) := by
    intro c
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalColimit_iff_oppositeLocalLimit δ F₀ c).2 (hlim (SSet.opObjEquiv.symm c))
  obtain ⟨F, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits δ F₀ hcol
  exact ⟨SSet.opFunctor.map F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftOppositeTransformation δ F₀ F β,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLeftKanExtension_opposite hβ⟩

/-- 概要：各点の標準局所図式が極限を持てば右 Kan 拡張が存在する。
方針：反転したデータへ存在定理を適用し、反転関手の二乗の等式で元のデータへ戻す。
規約：δ の fibration 性や単射性は要求しない。
使われ方：指定変換つき右 Kan 拡張の点ごとの存在からの組み立て。 -/
lemma exists_kanRightExtension_of_local_limits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hlim : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c)) :
    ∃ (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α := by
  have h := exists_kanRightExtension_op_of_local_limits
    (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
  change (∀ c : (SSet.opFunctor ⋙ SSet.opFunctor).obj C _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram ((SSet.opFunctor ⋙ SSet.opFunctor).map δ)
        ((SSet.opFunctor ⋙ SSet.opFunctor).map F₀) c)) →
    ∃ (F : (SSet.opFunctor ⋙ SSet.opFunctor).obj C ⟶
        (SSet.opFunctor ⋙ SSet.opFunctor).obj D)
      (α : SSet.Homotopy ((SSet.opFunctor ⋙ SSet.opFunctor).map δ ≫ F)
        ((SSet.opFunctor ⋙ SSet.opFunctor).map F₀)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension ((SSet.opFunctor ⋙ SSet.opFunctor).map δ)
        ((SSet.opFunctor ⋙ SSet.opFunctor).map F₀) F α at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square] at h
  exact h hlim

/-- 概要：右 Kan 拡張の存在は各点の標準局所図式の極限の存在と同値。
方針：必要性は各点の極限の値、十分性は双対化による coherent な組み立てを使う。
規約：K・C・D は同じ宇宙の quasicategory。
使われ方：右 Kan 拡張の存在の点ごとの判定。 -/
lemma exists_kanRightExtension_iff_local_limits {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] (δ : K ⟶ C) (F₀ : K ⟶ D) :
    (∃ (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c) := by
  constructor
  · rintro ⟨F, α, h⟩ c
    obtain ⟨t, ht, _⟩ := h.limitValue c
    exact ⟨t, ht⟩
  · exact exists_kanRightExtension_of_local_limits δ F₀

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
