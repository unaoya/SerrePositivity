module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.HomotopyPullback
public import SerrePositivity.KST.Comparison.FiberwisePullback

/-!
# Kan fibration の厳密引き戻しとホモトピー引き戻し

概要：元の右射が Kan fibration なら厳密引き戻しから置換模型への比較射は局所化同型となる。
方針：anodyne 分解の基底上の収縮を引き戻し、実ホモトピーから逆射を得る。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 のホモトピー引き戻しの計算。
使われ方：行ごとの積射影と骨格の比較。
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
概要：Kan fibration に沿う厳密引き戻しは指定したホモトピー引き戻し模型を計算する。
方針：分解の基底上のレトラクションと収縮を引き戻して、標準比較射の逆を構成する。
規約：Segal 1974 Proposition 1.6・Lemma 1.7。基底の Kan 性は不要。
使われ方：bar の各行の射影のホモトピー引き戻し性。
-/
theorem fibrantPullbackComparison_isIso {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : SSet.modelCategoryQuillen.J.rlp g) :
    IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison
      (show CommSq (pullback.fst f g) (pullback.snd f g) f g from ⟨pullback.condition⟩))) := by
  let d := AnodyneKanReplacement.factorization.factorizationData g
  obtain ⟨r, hir, hrg, H, _, hH⟩ :=
    anodyne_fibration_retraction d.i d.hi g hg d.p d.hp d.fac
  let sq : CommSq (pullback.fst f g) (pullback.snd f g) f g := ⟨pullback.condition⟩
  let j : pullback f g ⟶ pullback f d.p := homotopyPullbackComparison sq
  let t : pullback f d.p ⟶ pullback f g :=
    pullback.lift (pullback.fst f d.p) (pullback.snd f d.p ≫ r) (by
      rw [Category.assoc, hrg]
      exact pullback.condition)
  have hjf : j ≫ pullback.fst f d.p = pullback.fst f g := homotopyPullbackComparison_fst sq
  have hjs : j ≫ pullback.snd f d.p = pullback.snd f g ≫ d.i := homotopyPullbackComparison_snd sq
  have htf : t ≫ pullback.fst f g = pullback.fst f d.p := pullback.lift_fst ..
  have hts : t ≫ pullback.snd f g = pullback.snd f d.p ≫ r := pullback.lift_snd ..
  have hjt : j ≫ t = 𝟙 (pullback f g) := by
    apply pullback.hom_ext
    · rw [Category.assoc, htf, hjf, Category.id_comp]
    · rw [Category.assoc, hts, ← Category.assoc, hjs, Category.assoc, hir,
        Category.comp_id, Category.id_comp]
  have hrip : (r ≫ d.i) ≫ d.p = d.p := by rw [Category.assoc, d.fac, hrg]
  have hend : pullbackMapOver d.p f (r ≫ d.i) hrip = t ≫ j := by
    apply pullback.hom_ext
    · rw [pullbackMapOver_fst, Category.assoc, hjf, htf]
    · rw [pullbackMapOver_snd, Category.assoc, hjs]
      rw [← Category.assoc t (pullback.snd f g) d.i, hts, Category.assoc]
  have H' : SSet.Homotopy (𝟙 (pullback f d.p)) (t ≫ j) := by
    simpa only [pullbackMapOver_id, hend] using
      pullbackHomotopyOver d.p f (Category.id_comp d.p) hrip H hH
  exact (AnodyneHomotopy.mapRetractionIso AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) t j hjt H').isIso_inv
/--
概要：右射が Kan fibration の厳密な引き戻し四角形はホモトピー引き戻しである。
方針：標準引き戻しとの同型を標準比較射へ合成し、比較射の局所化可逆性を使う。
規約：Segal 1974 Proposition 1.6・Lemma 1.7。基底の Kan 性は不要。
使われ方：bar の各行の四角形の比較。
-/
theorem isHomotopyPullback_of_fibration {P X Y Z : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hg : SSet.modelCategoryQuillen.J.rlp g) :
    IsHomotopyPullback sq.toCommSq := by
  let c : CommSq (pullback.fst f g) (pullback.snd f g) f g := ⟨pullback.condition⟩
  have hfac : sq.isoPullback.hom ≫ homotopyPullbackComparison c =
      homotopyPullbackComparison sq.toCommSq := by
    apply pullback.hom_ext
    · rw [Category.assoc, homotopyPullbackComparison_fst, sq.isoPullback_hom_fst,
        homotopyPullbackComparison_fst]
    · rw [Category.assoc, homotopyPullbackComparison_snd,
        ← Category.assoc, sq.isoPullback_hom_snd, homotopyPullbackComparison_snd]
  have : IsIso (AnodyneHomotopy.anodyneQ.map (homotopyPullbackComparison c)) :=
    fibrantPullbackComparison_isIso f g hg
  dsimp only [IsHomotopyPullback]
  rw [← hfac, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance


end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.3.3.13" (partial := special) "仮定：単体集合の引き戻し四角形と右辺が Kan ファイブレーション（Lean が強い：HA の categorical fibration を Kan に限定。底の Kan 性は不要）。結論：標準比較が anodyne 局所化で可逆なホモトピー引き戻し（頂点への引き戻しで HA の結論に一致）。"] _root_.SerrePositivity.KST.Comparison.isHomotopyPullback_of_fibration
