module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndPresheafReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceSmallLimits
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableLimitCharacterization

/-!
概要：presentable ∞ 圏の全小極限の存在と、元の全錐の表現可能関手による判定。
方針：前層反映された Ind 模型で極限を構成し、全同値で戻して F1 の検出定理へ接続する。
規約：余完備性は presentable の定義から回収し、完備性を新たな仮定にしない。
使われ方：随伴関手定理と presentable 圏内の元の小図式の計算。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：presentable 圏は全小極限を持つ。
方針：元の余完備な小さい Ind 同値で、前層反映模型の完備性を移す。
規約：Ind の交換条件や反映の存在を入力に追加しない。
使われ方：presentable 圏の完備性の公開入口。 -/
lemma IsPresentable.hasSmallLimits {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C := by
  obtain ⟨κ, hκ, A, hA, hcolim, ⟨e⟩⟩ := (isPresentable_iff_cocompleteIndEquivalence C).mp hC
  have := hA
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact (ind_hasSmallLimits_of_hasSmallColimits hcolim).of_equivalence e

/-- 概要：元の任意小図式の native な極限が存在する。
方針：全小極限の存在を元の持ち上げ図式へ特殊化する。
規約：同値な別図式へ結論を変更しない。
使われ方：指定図式の極限錐の選択。 -/
lemma IsPresentable.hasLimit {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {K : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) : HasLimit D :=
  hC.hasSmallLimits K D

/-- 概要：presentable 圏の元の小極限は全表現可能関手で検出される。
方針：構成した極限存在に F1 の全共変表現可能関手による検出を合わせる。
規約：表現可能関手の標的は元の圏の宇宙に対応する空間圏。
使われ方：任意の元の候補全錐の極限判定。 -/
lemma presentable_isLimitCone_iff_representables {C : SSet.{u + 1}} [Quasicategory C]
    {K : SSet.{u}} {D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C} (c : JoinCone D) :
    IsLimitCone c ↔ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (covariantRepresentableInfinity x)
        (JoinCone.ulift.{u + 1, u + 2} c)) :=
  isLimitCone_iff_covariantRepresentableInfinity c

/-- 概要：元の presentable 小図式には全表現可能関手で極限となる全錐が存在する。
方針：構成した元の極限錐に既存の保存・検出定理を適用する。
規約：元の圏の完備性を入力にしない。
使われ方：表現可能性による極限構成の利用界面。 -/
lemma IsPresentable.exists_limitCone_representables {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {K : SSet.{u}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    ∃ c : JoinCone D, IsLimitCone c ∧ ∀ x : C _⦋0⦌,
      IsLimitCone (mapJoinCone (covariantRepresentableInfinity x)
        (JoinCone.ulift.{u + 1, u + 2} c)) := by
  obtain ⟨c, hc⟩ := hC.hasLimit D
  exact ⟨c, hc, (presentable_isLimitCone_iff_representables c).mp hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
