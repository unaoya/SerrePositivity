module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaYonedaColimitPreservationCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoproductsOnBaseIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanSiftedPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanExtension

/-!
概要：元の P_Σ 左 Kan 延長の全小余極限保存を元の底上の有限余積保存で判定する。
方針：実証済みの sifted 保存と元の指定単位の可逆性を完成した有限条件判定へ接続する。
規約：元の延長・指定単位・元の小さい底を保持する。
使われ方：HTT 5.5.8.15 の有限余積条件の元の全関手での公開界面。

対応節は Kerodon 8.4（Tag 03V7）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion


/-- 概要：指定した元の左 Kan 延長は元の底の有限余積を保つ場合ちょうど全小余極限を保つ。
方針：指定単位の回収同型と元の延長の sifted 保存を全保存判定へ適用する。
規約：有限条件は元の F₀ に課し、延長の保存性を追加入力にしない。
使われ方：P_Σ の左 Kan 延長の全小余極限保存判定。 -/
lemma sigmaLeftKanExtension_preservesSmallColimits_iff
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (hD : ∀ (I : Type u) [Finite I]
      (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesFiniteCoproductsOnBase F₀ := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtension_preservesSmallSiftedColimits β hβ
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtensionRecoveryIso β hβ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_sifted hC hD G).trans
    ⟨fun h ↦ h.1.of_functorIso e, fun h ↦ ⟨h.of_functorIso e.symm, hs⟩⟩

/-- 概要：余完備な標的への元の左 Kan 延長の全保存は元の有限余積保存に同値。
方針：元の標的の全小余極限存在から有限余積の存在を取り出す。
規約：指定単位と元の F₀ を保つ。
使われ方：presentable な標的への P_Σ 延長の有限判定。 -/
lemma sigmaLeftKanExtension_preservesSmallColimits_iff_of_cocomplete
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservesFiniteCoproductsOnBase F₀ :=
  sigmaLeftKanExtension_preservesSmallColimits_iff hC
    (fun I _ ↦ hD (nerve (Discrete I))) β hβ

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
