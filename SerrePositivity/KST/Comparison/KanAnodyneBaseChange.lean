module

public import SerrePositivity.KST.Comparison.HornPreimage
public import SerrePositivity.KST.Comparison.OverHornLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass

/-!
# anodyne 射の Kan fibration に沿う基底変換

概要：anodyne 射を Kan fibration に沿って引き戻すと局所化同型となる。
方針：スライスの積と忘却の右随伴に、局所化可逆な単射を検出する右テストを移す。
規約：Segal 1974 Proposition 1.6 の対角模型の補助。Moss 2020 Theorem 42 の
strong anodyne 性より弱い結論を、horn の同時収縮と随伴から証明する。
使われ方：ホモトピー引き戻しと骨格の貼り合わせの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：Kan fibration とのスライス内の積は基底付き horn 包含を anodyne 射に送る。
方針：horn の逆像の二段階の収縮による anodyne 性を標準引き戻しへ適用する。
規約：Moss arXiv:1506.04887v2 Theorem 5.1 の strong 性は要求しない。
使われ方：右随伴の全ての Kan fibration の保存。
-/
theorem sliceFiberFunctor_horn_anodyne {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {n : ℕ} (k : Fin (n + 2))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ B) :
    SSet.anodyneExtensions ((sliceFiberFunctor p).map (hornOverMap k b)) := by
  have hpb : SSet.modelCategoryQuillen.J.rlp (pullback.fst b p) :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst b p hp
  exact pullback_horn_anodyne k (pullback.fst b p) hpb _ _
    (sliceFiberFunctor_map_isPullback p (hornOverMap k b))

/--
概要：Kan fibration に沿う積の右随伴は任意の Kan fibration を保つ。
方針：基底付き horn の逆像の anodyne 性に随伴の持ち上げ性の対応を適用する。
規約：基底は Kan とは限らない。右の入力は任意の Kan fibration。
使われ方：anodyne 射の基底変換。
-/
theorem sliceFiberRightAdjoint_rlp {E B K L : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (q : K ⟶ L)
    (hq : SSet.modelCategoryQuillen.J.rlp q) :
    SSet.modelCategoryQuillen.J.rlp (((sliceFiberFunctor p).rightAdjoint.map q).left) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  apply underlying_rlp_of_over_horns
  intro n k b
  apply (adj.hasLiftingProperty_iff (hornOverMap k b) q).mp
  exact sliceFiberFunctor_horn_anodyne p hp k b _ hq

/--
概要：スライス内の anodyne 射の Kan fibration との積は anodyne である。
方針：右随伴の Kan fibration の保存から、左随伴の左持ち上げ性の保存を得る。
規約：基底や全空間の Kan 性を要求しない。
使われ方：任意の anodyne 射の Kan 基底変換。
-/
theorem sliceFiberFunctor_anodyne {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {X Y : Over B} (i : X ⟶ Y)
    (hi : SSet.anodyneExtensions i.left) :
    SSet.anodyneExtensions ((sliceFiberFunctor p).map i) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro K L q hq
  exact (adj.hasLiftingProperty_iff i q).mpr
    (over_lifting_of_underlying i (G.map q) (hi _ (sliceFiberRightAdjoint_rlp p hp q hq)))

/--
概要：anodyne 射の Kan fibration に沿う任意の引き戻しは anodyne である。
方針：スライスの積の anodyne 性を標準射影と引き戻しの一意な同型で移す。
規約：Moss arXiv:1506.04887v2 §5 の anodyne 性。strong 性は主張しない。
使われ方：ホモトピー引き戻しの模型の基底変換。
-/
theorem pullback_anodyne {A B E P : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k p i) :
    SSet.anodyneExtensions j := by
  let f : Over.mk i ⟶ Over.mk (𝟙 B) := Over.homMk i
  have hf : SSet.anodyneExtensions ((sliceFiberFunctor p).map f) :=
    sliceFiberFunctor_anodyne p hp f hi
  have hs : (sliceFiberFunctor p).map f ≫ pullback.snd (𝟙 B) p = pullback.snd i p :=
    sliceFiberFunctor_map_snd p f
  have ht : SSet.anodyneExtensions (pullback.snd i p) := by
    rw [← hs]
    exact SSet.anodyneExtensions.comp_mem _ _ hf (SSet.anodyneExtensions.of_isIso _)
  let e := sq.isoIsPullback _ _ (IsPullback.of_hasPullback i p).flip
  have he : e.hom ≫ pullback.snd i p = j := sq.isoIsPullback_hom_fst ..
  rw [← he]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _) ht

/--
概要：Kan fibration とのスライス内の積は基底付き horn 包含を局所化同型に送る。
方針：horn の逆像の収縮を、積が作る厳密な引き戻し四角形に適用する。
規約：Segal 1974 Proposition 1.6 の基底変換の生成射での確認。
使われ方：随伴の右側が Kan 条件を満たすこと。
-/
theorem sliceFiberFunctor_horn_localized_isIso {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {n : ℕ} (k : Fin (n + 2))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ B) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map (hornOverMap k b))) := by
  have hpb : SSet.modelCategoryQuillen.J.rlp (pullback.fst b p) :=
    SSet.modelCategoryQuillen.J.rlp.pullback_fst b p hp
  exact pullback_horn_localized_isIso k (pullback.fst b p) hpb _ _
    (sliceFiberFunctor_map_isPullback p (hornOverMap k b))

/--
概要：基底変換の右随伴は検出用の右テスト射をスライス内の Kan fibration に送る。
方針：horn の逆像の局所化可逆性に随伴の持ち上げ性の対応を適用する。
規約：Segal 1974 Proposition 1.6 の基底付き比較の補助。
使われ方：anodyne 射と Kan 基底上の局所化可逆な単射の移送。
-/
theorem sliceFiberRightAdjoint_test_rlp {E B K L : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (q : K ⟶ L)
    (hq : KanTestLiftingClass.rightTests q) :
    SSet.modelCategoryQuillen.J.rlp (((sliceFiberFunctor p).rightAdjoint.map q).left) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  apply underlying_rlp_of_over_horns
  intro n k b
  apply (adj.hasLiftingProperty_iff (hornOverMap k b) q).mp
  have : Mono (hornOverMap k b).left := inferInstanceAs (Mono (Λ[n + 1, k]).ι)
  have hs := sliceFiberFunctor_map_isPullback p (hornOverMap k b)
  have : Mono (F.map (hornOverMap k b)) := hs.mono_fst_of_mono
  exact KanTestLiftingClass.localizedMono_le_llp _
    ⟨inferInstance, sliceFiberFunctor_horn_localized_isIso p hp k b⟩ q hq

/--
概要：スライス内の anodyne 射の Kan fibration との積は局所化同型となる。
方針：右随伴が検出用の右テスト射を Kan fibration に送ることを horn ごとに示す。
規約：局所化の余極限保存やモデル構造の公理を仮定しない。
使われ方：任意の anodyne 射の Kan 基底変換。
-/
theorem sliceFiberFunctor_anodyne_localized_isIso {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {X Y : Over B} (i : X ⟶ Y)
    (hi : SSet.anodyneExtensions i.left) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map i)) := by
  let F := sliceFiberFunctor p
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  apply KanTestLiftingClass.localized_isIso_of_llp
  intro K L q hq
  have hGq := sliceFiberRightAdjoint_test_rlp p hp q hq
  exact (adj.hasLiftingProperty_iff i q).mpr
    (over_lifting_of_underlying i (G.map q) (hi _ hGq))

/--
概要：anodyne 射の Kan fibration に沿う任意の厳密引き戻しは局所化同型である。
方針：終対象へのスライスの射として表し、固定したファイバーとの積の結果を適用する。
規約：Segal 1974 Proposition 1.6 の補助。基底・全空間の Kan 性は要求しない。
使われ方：ホモトピー引き戻しの模型の基底変換。
-/
theorem pullback_anodyne_localized_isIso {A B E P : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k p i) :
    IsIso (AnodyneHomotopy.anodyneQ.map j) := by
  let f : Over.mk i ⟶ Over.mk (𝟙 B) := Over.homMk i
  have hf : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor p).map f)) :=
    sliceFiberFunctor_anodyne_localized_isIso p hp f hi
  have hs : (sliceFiberFunctor p).map f ≫ pullback.snd (𝟙 B) p = pullback.snd i p :=
    sliceFiberFunctor_map_snd p f
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map (pullback.snd i p)) := by
    rw [← hs, Functor.map_comp]
    infer_instance
  let e := sq.isoIsPullback _ _ (IsPullback.of_hasPullback i p).flip
  have he : e.hom ≫ pullback.snd i p = j := sq.isoIsPullback_hom_fst ..
  rw [← he, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
