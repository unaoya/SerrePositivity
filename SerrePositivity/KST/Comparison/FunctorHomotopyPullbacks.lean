module

public import SerrePositivity.KST.Comparison.AlternativePullback

/-!
# 分解と厳密ファイバーを保つ関手のホモトピー引き戻し

概要：厳密な引き戻しと anodyne–Kan 分解、局所化同型を保つ関手はホモトピー引き戻しを保つ。
方針：別分解の比較射を、元の比較射の像と引き戻しの普遍性の同型で表示する。
規約：Segal 1974 Proposition 1.6 の単体・境界との積に使う一般的な補助。
使われ方：固定した単体集合との直積に具体的な保存則を与えて適用する。
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
概要：厳密ファイバーと anodyne–Kan 分解を保つ関手はホモトピー引き戻しを保つ。
方針：比較射を関手へ送り、引き戻しの普遍性の同型と合成する。
規約：各保存則は任意の射・厳密な四角形に対するもので、中心の貼り合わせ定理は仮定しない。
使われ方：骨格の付着の単体・境界との直積。
-/
theorem isHomotopyPullback_map_of_preserves_factorizations (T : SSet.{u} ⥤ SSet.{u})
    (hPB : ∀ {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B},
      IsPullback a b f g → IsPullback (T.map a) (T.map b) (T.map f) (T.map g))
    (hA : ∀ {X Y : SSet.{u}} (i : X ⟶ Y), SSet.anodyneExtensions i →
      SSet.anodyneExtensions (T.map i))
    (hF : ∀ {X Y : SSet.{u}} (p : X ⟶ Y), SSet.modelCategoryQuillen.J.rlp p →
      SSet.modelCategoryQuillen.J.rlp (T.map p))
    (hW : ∀ {X Y : SSet.{u}} (w : X ⟶ Y), IsIso (AnodyneHomotopy.anodyneQ.map w) →
      IsIso (AnodyneHomotopy.anodyneQ.map (T.map w)))
    {P X Y B : SSet.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g) (h : IsHomotopyPullback sq) :
    IsHomotopyPullback (T.map_commSq sq) := by
  let dp := AnodyneKanReplacement.factorization.factorizationData g
  let k := alternativePullbackComparison sq dp.i dp.p dp.fac
  have hk : IsIso (AnodyneHomotopy.anodyneQ.map k) :=
    (isHomotopyPullback_iff_alternative sq dp.i dp.hi dp.p dp.hp dp.fac).mp h
  let hp := hPB (IsPullback.of_hasPullback f dp.p)
  let e := hp.isoPullback
  have heF : e.hom ≫ pullback.fst (T.map f) (T.map dp.p) = T.map (pullback.fst f dp.p) :=
    hp.isoPullback_hom_fst
  have heS : e.hom ≫ pullback.snd (T.map f) (T.map dp.p) = T.map (pullback.snd f dp.p) :=
    hp.isoPullback_hom_snd
  have hfac : T.map dp.i ≫ T.map dp.p = T.map g := by rw [← T.map_comp, dp.fac]
  have he : T.map k ≫ e.hom =
      alternativePullbackComparison (T.map_commSq sq) (T.map dp.i) (T.map dp.p) hfac := by
    apply pullback.hom_ext
    · rw [Category.assoc, heF, ← T.map_comp, alternativePullbackComparison_fst,
        alternativePullbackComparison_fst]
    · rw [Category.assoc, heS, ← T.map_comp, alternativePullbackComparison_snd,
        T.map_comp, alternativePullbackComparison_snd]
  apply (isHomotopyPullback_iff_alternative (T.map_commSq sq) (T.map dp.i)
    (hA _ dp.hi) (T.map dp.p) (hF _ dp.hp) hfac).mpr
  rw [← he, Functor.map_comp]
  have := hW k hk
  infer_instance

end SerrePositivity.KST.Comparison
