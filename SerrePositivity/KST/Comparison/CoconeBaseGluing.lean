module

public import SerrePositivity.KST.Comparison.CoconeBaseComparison
public import SerrePositivity.KST.Comparison.SpanCylinderColimitNaturality
public import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry

/-!
# 固定射へのホモトピー引き戻しの有限貼り合わせ

概要：単射な右脚の span の各項で同じ固定射への四角形がホモトピー引き戻しなら、余極限でもそうなる。
方針：指定した Kan 分解への標準比較を余極限へ貼り合わせる。
規約：Segal 1974 Proposition 1.6 の境界の有限被覆の比較。
使われ方：境界の各面とその交叉から境界全体への移行。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：固定した射への各項のホモトピー引き戻しは、単射な脚の余極限へ貼り合わさる。
方針：固定射の anodyne–Kan 分解、スライスの厳密ファイバーの余極限保存、比較射の貼り合わせを使う。
規約：頂点・交叉の三項の仮定を明示し、境界全体の結論は仮定しない。
使われ方：fat realization の有限骨格の境界の比較。
-/
theorem coconeBase_homotopyPullback_of_span
    {A Y : WalkingSpan ⥤ SSet.{u}}
    [Mono (A.map WalkingSpan.Hom.snd)] [Mono (Y.map WalkingSpan.Hom.snd)]
    (cA : Cocone A) (hcA : IsColimit cA) (cY : Cocone Y) (hcY : IsColimit cY)
    (b : A ⟶ Y) (b₀ : cA.pt ⟶ cY.pt)
    (hb : ∀ d, cA.ι.app d ≫ b₀ = b.app d ≫ cY.ι.app d)
    {X B : SSet.{u}} {a : cA.pt ⟶ X} {f : X ⟶ B} {g : cY.pt ⟶ B}
    (sq : CommSq a b₀ f g)
    (hlocal : ∀ d, IsHomotopyPullback (coconeBaseSquare cA cY b b₀ hb sq d)) :
    IsHomotopyPullback sq := by
  let dp := AnodyneKanReplacement.factorization.factorizationData f
  let k := coconeBaseFiberComparison cA cY b b₀ hb sq dp.i dp.p dp.fac
  have hk d : IsIso (AnodyneHomotopy.anodyneQ.map (k.app d)) :=
    (isHomotopyPullback_iff_alternative
      (coconeBaseSquare cA cY b b₀ hb sq d).flip dp.i dp.hi dp.p dp.hp dp.fac).mp
        ((isHomotopyPullback_flip_iff (coconeBaseSquare cA cY b b₀ hb sq d)).mpr (hlocal d))
  let : Mono (((coconeOverDiagram cY g).map WalkingSpan.Hom.snd).left) :=
    inferInstanceAs (Mono (Y.map WalkingSpan.Hom.snd))
  let : Mono ((coconeOverDiagram cY g ⋙ sliceFiberFunctor dp.p).map WalkingSpan.Hom.snd) :=
    (sliceFiberFunctor_map_isPullback dp.p
      ((coconeOverDiagram cY g).map WalkingSpan.Hom.snd)).mono_fst_of_mono
  have hcmp := spanColimit_map_localized_isIso k hk cA hcA
    (fiberCocone dp.p cY g) (fiberCoconeIsColimit dp.p cY hcY g)
    (alternativePullbackComparison sq.flip dp.i dp.p dp.fac)
    (coconeBaseFiberComparison_cocone cA cY b b₀ hb sq dp.i dp.p dp.fac)
  exact (isHomotopyPullback_flip_iff sq).mp
    ((isHomotopyPullback_iff_alternative sq.flip dp.i dp.hi dp.p dp.hp dp.fac).mpr hcmp)

end SerrePositivity.KST.Comparison
