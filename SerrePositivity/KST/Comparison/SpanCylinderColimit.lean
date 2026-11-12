module

public import SerrePositivity.KST.Comparison.DoubleMappingCylinderCollapse
public import SerrePositivity.KST.Comparison.SpanCylinderFunctor

/-!
# span の余極限への二重写像円筒の比較

概要：任意の具体的な余極限の余錐へ円筒を潰し、各頂点との可換性と自然性を示す。
方針：通常の pushout への比較を、余極限の普遍性の同型へ合成する。
規約：Segal 1974 Lemma 1.7 を通常の単射に沿う付着へ移す補助。
使われ方：有限骨格の実際の pushout のホモトピー引き戻し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：span の二重写像円筒から具体的な余極限の頂点への比較。
方針：通常の pushout へ潰し、その普遍性の同型で指定の余極限へ移す。
規約：余錐とその普遍性は明示的な引数。
使われ方：有限骨格など既存の実対象への比較。
-/
def spanCylinderToColimit (F : WalkingSpan ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c) :
    spanCylinderFunctor.obj F ⟶ c.pt :=
  doubleMappingCylinderCollapse (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) ≫
    (IsPushout.of_isColimit_cocone hc).isoPushout.inv

/--
概要：余極限への比較は左頂点の構造写像を保つ。
方針：円筒を潰す計算則と余極限の同型の計算則を使う。
規約：左頂点の対象はそのまま。
使われ方：四頂点の比較の可換性。
-/
@[reassoc] theorem spanCylinderLeft_toColimit (F : WalkingSpan ⥤ SSet.{u})
    (c : Cocone F) (hc : IsColimit c) :
    spanCylinderLeft.app F ≫ spanCylinderToColimit F c hc = c.ι.app .left := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (F.map WalkingSpan.Hom.fst)
      (F.map WalkingSpan.Hom.snd) ≫
      (doubleMappingCylinderCollapse (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) ≫
        (IsPushout.of_isColimit_cocone hc).isoPushout.inv) = c.ι.app .left := by
    rw [← Category.assoc, doubleMappingCylinder_left_collapse]
    exact (IsPushout.of_isColimit_cocone hc).inl_isoPushout_inv
  exact h

/--
概要：余極限への比較は右頂点の構造写像を保つ。
方針：円筒を潰す計算則と余極限の同型の計算則を使う。
規約：右頂点の対象はそのまま。
使われ方：四頂点の比較の可換性。
-/
@[reassoc] theorem spanCylinderRight_toColimit (F : WalkingSpan ⥤ SSet.{u})
    (c : Cocone F) (hc : IsColimit c) :
    spanCylinderRight.app F ≫ spanCylinderToColimit F c hc = c.ι.app .right := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (F.map WalkingSpan.Hom.fst)
      (F.map WalkingSpan.Hom.snd) ≫
      (doubleMappingCylinderCollapse (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) ≫
        (IsPushout.of_isColimit_cocone hc).isoPushout.inv) = c.ι.app .right := by
    rw [← Category.assoc, doubleMappingCylinder_right_collapse]
    exact (IsPushout.of_isColimit_cocone hc).inr_isoPushout_inv
  exact h

/--
概要：中央の円筒を余極限へ送ると区間を忘れて中央の構造写像になる。
方針：円筒の収縮と余錐の中央・左の可換性を合わせる。
規約：標準区間は第一射影で忘れる。
使われ方：比較の span の射に関する自然性。
-/
@[reassoc] theorem spanCylinder_middle_toColimit (F : WalkingSpan ⥤ SSet.{u})
    (c : Cocone F) (hc : IsColimit c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd) ≫
      spanCylinderToColimit F c hc = fst (F.obj .zero) (Δ[1] : SSet.{u}) ≫ c.ι.app .zero := by
  have hP := (IsPushout.of_isColimit_cocone hc).inl_isoPushout_inv
  rw [spanCylinderToColimit, ← Category.assoc, doubleMappingCylinder_middle_collapse]
  simp only [Category.assoc, hP, c.w WalkingSpan.Hom.fst]

/--
概要：余極限への比較は全ての頂点の構造写像を保つ。
方針：中央・左・右を場合分けして包含の式を使う。
規約：中央は左の射を経由する円筒の零端点。
使われ方：Lemma 1.7 の各頂点の結論の輸送。
-/
@[reassoc] theorem spanCylinderVertex_toColimit (F : WalkingSpan ⥤ SSet.{u})
    (c : Cocone F) (hc : IsColimit c) (d : WalkingSpan) :
    (spanCylinderVertex d).app F ≫ spanCylinderToColimit F c hc = c.ι.app d := by
  rcases d with (_ | _ | _)
  · change (F.map WalkingSpan.Hom.fst ≫ spanCylinderLeft.app F) ≫ _ = _
    rw [Category.assoc, spanCylinderLeft_toColimit]
    exact c.w WalkingSpan.Hom.fst
  · exact spanCylinderLeft_toColimit F c hc
  · exact spanCylinderRight_toColimit F c hc

/--
概要：右の脚が単射の span では、円筒から具体的な余極限への比較は局所化同型である。
方針：通常の pushout への可逆性と余極限の同型を合成する。
規約：左の脚の単射性や各対象の Kan 性は不要。
使われ方：円筒のホモトピー引き戻しから通常の付着への移送。
-/
theorem spanCylinderToColimit_localized_isIso (F : WalkingSpan ⥤ SSet.{u})
    (c : Cocone F) (hc : IsColimit c) [Mono (F.map WalkingSpan.Hom.snd)] :
    IsIso (AnodyneHomotopy.anodyneQ.map (spanCylinderToColimit F c hc)) := by
  rw [spanCylinderToColimit, Functor.map_comp]
  have := doubleMappingCylinderCollapse_localized_isIso
    (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  infer_instance

end SerrePositivity.KST.Comparison
