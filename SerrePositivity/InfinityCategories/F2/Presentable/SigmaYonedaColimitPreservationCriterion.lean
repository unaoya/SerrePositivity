module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteCoproductPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricPreservation

/-!
概要：P_Σ の全小余極限保存を元の Yoneda 制限上の有限余積条件へ縮約する。
方針：有限余積の全比較による判定を、有限余積と sifted 余極限の一般保存判定へ接続する。
規約：元の小さい底・元の Yoneda・元の指定余錐を保持する。
使われ方：元の左 Kan 延長の全小余極限保存と HTT 5.5.8.15 の有限条件。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：全小余極限保存は元の Yoneda 制限上の有限余積保存と sifted 保存に同値。
方針：元の有限余積比較を生成で可逆にし、全小余極限の一般判定へ渡す。
規約：有限余積条件は P_Σ 全体ではなく元の小さい底で検査する。
使われ方：元の P_Σ 関手の全余極限保存の公開判定。 -/
lemma sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_sifted
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : ∀ (I : Type u) [Finite I]
      (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D), HasColimit p)
    (G : SigmaPresheafInfinity C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔
      PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G) ∧
        PreservesSmallSiftedColimits G := by
  constructor
  · intro h
    exact ⟨sigma_yoneda_preservesFiniteCoproductsOnBase G
      (fun I _ p c hc ↦ h (nerve (Discrete I)) p c hc), fun I _ p c hc ↦ h I p c hc⟩
  · rintro ⟨hfin, hsift⟩
    exact preservesSmallColimits_of_finiteCoproducts_sifted (sigma_hasSmallCoproducts hC) G
      (sigma_preservesFiniteCoproducts_of_yoneda hC hD G
        (preservesSmallFiltered_of_sifted hsift)
        (preservesSmallGeometric_of_sifted hsift) hfin) hsift

/-- 概要：余完備な標的では全小余極限保存を元の Yoneda 制限と sifted 保存で判定する。
方針：標的の全小余極限存在から有限形状の存在を取り出す。
規約：標的の余完備性を明示し、元の小さい底で有限条件を検査する。
使われ方：presentable な標的への元の関手の判定。 -/
lemma sigma_preservesSmallColimits_iff_yoneda_of_cocomplete
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D) (G : SigmaPresheafInfinity C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔
      PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G) ∧
        PreservesSmallSiftedColimits G :=
  sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_sifted hC
    (fun I _ ↦ hD (nerve (Discrete I))) G

/-- 概要：filtered・実現保存関手の全小余極限保存は元の Yoneda 制限の有限条件に同値。
方針：弱い二種類の保存から sifted 保存を得て、完成した有限条件判定を使う。
規約：標的の有限余積・filtered 余極限・実現の存在を明示する。
使われ方：HTT 5.5.8.15 の filtered／幾何学的実現版の判定。 -/
lemma sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hDcop : ∀ (I : Type u) [Finite I]
      (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D), HasColimit p)
    (hDf : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hDg : HasSmallGeometricRealizations D) (G : SigmaPresheafInfinity C ⟶ D)
    (hGf : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hGg : PreservesSmallGeometricRealizations G) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits G ↔
      PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G) := by
  have hs := sigma_preservesSmallSiftedColimits_of_filtered_geometric hC hDf hDg G hGf hGg
  exact (sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_sifted hC hDcop G).trans
    ⟨And.left, fun h ↦ ⟨h, hs⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
