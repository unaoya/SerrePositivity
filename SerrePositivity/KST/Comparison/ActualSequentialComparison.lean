module

public import SerrePositivity.KST.Comparison.SequentialHomotopyPullback

/-!
# 具体的な順序余極限のホモトピー引き戻し

概要：標準の選択された余極限の比較を、任意の実際の余錐へ移す。
方針：余極限の普遍性の同型の自然性と、四頂点の同型不変性を使う。
規約：Segal 1974 Proposition 1.6 の fat realization の実対象への移送。
使われ方：骨格の包含の実際の余極限と定数図式の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：二つの具体的な余極限の普遍的な同型は、余錐に整合する射と可換。
方針：各標準余極限の構造射との合成を計算する。
規約：比較する射は余錐との可換性のみを要求する。
使われ方：ホモトピー引き戻しの四頂点を実際の余極限へ移す。
-/
theorem colimitCoconeIso_naturality {F G : ℕ ⥤ SSet.{u}} (α : F ⟶ G)
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (m : c.pt ⟶ d.pt) (hm : ∀ n, c.ι.app n ≫ m = α.app n ≫ d.ι.app n) :
    colim.map α ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom ≫ m := by
  apply colimit.hom_ext
  intro n
  have hF : colimit.ι F n ≫ ((colimit.isColimit F).coconePointUniqueUpToIso hc).hom =
      c.ι.app n := (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc n
  have hG : colimit.ι G n ≫ ((colimit.isColimit G).coconePointUniqueUpToIso hd).hom =
      d.ι.app n := (colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hd n
  rw [← Category.assoc, colimit.ι_map, Category.assoc, hG, ← Category.assoc, hF]
  exact (hm n).symm

/--
概要：各段階のホモトピー引き戻しは具体的な順序余極限の四角形へ移る。
方針：標準の余極限の比較を普遍的な四同型で移す。
規約：上側二図式の遷移の単射性を要求する。
使われ方：fat realization の有限骨格から無限骨格への比較。
-/
theorem actual_sequential_homotopyPullback {A X Y B : ℕ ⥤ SSet.{u}}
    {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g)
    (hA : ∀ n, Mono (SerrePositivity.SimplicialModel.SequentialBoundaryFactorization.stepMap A n))
    (hX : ∀ n, Mono (SerrePositivity.SimplicialModel.SequentialBoundaryFactorization.stepMap X n))
    (h : ∀ n, IsHomotopyPullback (CommSq.mk (congrArg (fun t => t.app n) sq.w)))
    (cA : Cocone A) (cX : Cocone X) (cY : Cocone Y) (cB : Cocone B)
    (hcA : IsColimit cA) (hcX : IsColimit cX) (hcY : IsColimit cY) (hcB : IsColimit cB)
    {a₀ : cA.pt ⟶ cX.pt} {b₀ : cA.pt ⟶ cY.pt}
    {f₀ : cX.pt ⟶ cB.pt} {g₀ : cY.pt ⟶ cB.pt} (sq₀ : CommSq a₀ b₀ f₀ g₀)
    (ha : ∀ n, cA.ι.app n ≫ a₀ = a.app n ≫ cX.ι.app n)
    (hb : ∀ n, cA.ι.app n ≫ b₀ = b.app n ≫ cY.ι.app n)
    (hf : ∀ n, cX.ι.app n ≫ f₀ = f.app n ≫ cB.ι.app n)
    (hg : ∀ n, cY.ι.app n ≫ g₀ = g.app n ≫ cB.ι.app n) :
    IsHomotopyPullback sq₀ := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    ((colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}).map_commSq sq) sq₀
    ((colimit.isColimit A).coconePointUniqueUpToIso hcA).hom
    ((colimit.isColimit X).coconePointUniqueUpToIso hcX).hom
    ((colimit.isColimit Y).coconePointUniqueUpToIso hcY).hom
    ((colimit.isColimit B).coconePointUniqueUpToIso hcB).hom
    (colimitCoconeIso_naturality a cA cX hcA hcX a₀ ha)
    (colimitCoconeIso_naturality b cA cY hcA hcY b₀ hb)
    (colimitCoconeIso_naturality f cX cB hcX hcB f₀ hf)
    (colimitCoconeIso_naturality g cY cB hcY hcB g₀ hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp
    (sequential_homotopyPullback sq hA hX h)

end SerrePositivity.KST.Comparison
