module

public import SerrePositivity.KST.Comparison.FunctorHomotopyPullbacks
public import SerrePositivity.KST.Comparison.FiniteOperationsFibrations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-!
# 固定した単体集合との積とホモトピー引き戻し

概要：任意の固定対象との直積はホモトピー引き戻しを保つ。
方針：厳密な引き戻しを各次数の組で確認し、分解と局所化同型の保存を使う。
規約：Segal 1974 Proposition 1.6 の単体・境界の付着。固定対象の Kan 性は不要。
使われ方：有限骨格の貼り合わせで単体と境界を掛ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.SimplicialModel

/--
概要：固定した右因子との直積は厳密な引き戻しを保つ。
方針：一致する固定因子の成分と、元の引き戻しの成分から元の組を復元する。
規約：四つの頂点に同じ固定因子を掛ける。
使われ方：直積のホモトピー引き戻しの保存の厳密な部分。
-/
theorem tensorRight_isPullback {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (h : IsPullback a b f g) (K : SSet.{u}) :
    IsPullback (a ▷ K) (b ▷ K) (f ▷ K) (g ▷ K) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
  have hd := h.map ev
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (congrArg (fun t => t.app d x.1) h.w) rfl
  · rintro ⟨x, k⟩ ⟨y, l⟩ ⟨h₁, h₂⟩
    change (a.app d x, k) = (a.app d y, l) at h₁
    change (b.app d x, k) = (b.app d y, l) at h₂
    exact Prod.ext (Types.ext_of_isPullback hd (congrArg Prod.fst h₁) (congrArg Prod.fst h₂))
      (congrArg (fun t : X.obj d × K.obj d => t.2) h₁)
  · rintro ⟨x, k⟩ ⟨y, l⟩ he
    change (f.app d x, k) = (g.app d y, l) at he
    obtain ⟨p, hp, hq⟩ := Types.exists_of_isPullback hd x y (congrArg Prod.fst he)
    have hk : k = l := congrArg (fun t : B.obj d × K.obj d => t.2) he
    exact ⟨(p, k), Prod.ext hp rfl, Prod.ext hq hk⟩

/--
概要：固定した右因子との直積はホモトピー引き戻しを保つ。
方針：厳密な引き戻しと anodyne–Kan 分解、局所化同型の保存に一般的な比較補題を使う。
規約：固定した単体集合の可縮性や Kan 性は不要。
使われ方：Segal Proposition 1.6 の標準単体と境界との積。
-/
theorem isHomotopyPullback_tensorRight {P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g) (h : IsHomotopyPullback sq) (K : SSet.{u}) :
    IsHomotopyPullback ((tensorRight K).map_commSq sq) :=
  isHomotopyPullback_map_of_preserves_factorizations (tensorRight K)
    (fun hs => tensorRight_isPullback hs K) (fun _ hi => hi.whiskerRight K)
    (fun p hp => tensorRight_rlp p hp K)
    (fun w hw => AnodyneHomotopy.whiskerRight_anodyneQ_isIso w hw K) sq h

end SerrePositivity.KST.Comparison
