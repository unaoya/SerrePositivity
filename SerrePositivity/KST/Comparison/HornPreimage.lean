module

public import SerrePositivity.KST.Comparison.HornContraction
public import SerrePositivity.KST.Comparison.PairHomotopyLifting
public import SerrePositivity.KST.Comparison.PairContractionAnodyne
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Kan fibration に沿う horn の逆像の局所化可逆性

概要：horn 包含の Kan fibration に沿う逆像は anodyne となる。
方針：horn を保つ min(x,k) を経由する二つの収縮を持ち上げる。
規約：Segal 1974 Proposition 1.6 の対角模型の補助。Moss 2020 §5 Theorem 42 の
strong anodyne 性を引用せず、anodyne 性を相対ホモトピーの持ち上げで証明する。
使われ方：ホモトピー引き戻しと骨格の貼り合わせを接続する。
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
概要：horn の添字にあたる頂点の定数単体は horn に含まれる。
方針：次元が正なら別の頂点 j があり、その頂点を定数単体は欠く。
規約：horn は正次元で扱う。零次元の空の horn には適用しない。
使われ方：収縮の終点が horn の逆像に入ること。
-/
theorem const_horn_vertex_mem {n : ℕ} [NeZero n] (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) (s : (Δ[n] : SSet.{u}).obj d) :
    (SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm k)).app d s ∈
      (Λ[n, k]).obj d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h01 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at h'
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ k := by
    by_cases h : k = 0
    · exact ⟨Fin.last n, fun h' => h01 ((h'.trans h).symm)⟩
    · exact ⟨0, Ne.symm h⟩
  rw [SSet.mem_horn_iff_notMem_range]
  refine ⟨j, hj, ?_⟩
  rintro ⟨i, hi⟩
  change k = j at hi
  exact hj hi.symm

/--
概要：Kan fibration に沿う正次元 horn の逆像の包含は anodyne である。
方針：標準単体と horn の同時収縮を持ち上げ、逆像を保つ二つの区間写像を得る。
規約：Segal 1974 Proposition 1.6 の補助。strong anodyne 性を仮定も結論もしない。
使われ方：Kan fibration に沿う基底変換とセルの比較。
-/
theorem horn_preimage_anodyne {n : ℕ} [NeZero n] (k : Fin (n + 1))
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) (hp : SSet.modelCategoryQuillen.J.rlp p) :
    SSet.anodyneExtensions ((Λ[n, k]).preimage p).ι := by
  let A := (Λ[n, k]).preimage p
  let H₀ := simplexMeetToIdentity.{u} k
  let H₁ := simplexMeetToVertex.{u} k
  have e₀ : intervalEndpoint E 0 = SSet.ι₁ := (AnodyneHomotopy.endpoint_one_factor E).symm
  have e₁ : intervalEndpoint E 1 = SSet.ι₀ := (AnodyneHomotopy.endpoint_zero_factor E).symm
  have hb₀ : (𝟙 E) ≫ p = intervalEndpoint E 0 ≫ (p ▷ (Δ[1] : SSet.{u}) ≫ H₀.h) := by
    rw [e₀, ← Category.assoc, SSet.ι₁_comp, Category.assoc, H₀.h₁,
      Category.comp_id, Category.id_comp]
  obtain ⟨h₀, h₀end, h₀base⟩ := interval_lift p hp 0 (𝟙 E)
    (p ▷ (Δ[1] : SSet.{u}) ≫ H₀.h) hb₀
  rw [e₀] at h₀end
  have hmeet : (SSet.ι₀ ≫ h₀) ≫ p = p ≫ simplexOrderMap (vertexMeet k) := by
    rw [Category.assoc, h₀base, ← Category.assoc, SSet.ι₀_comp, Category.assoc, H₀.h₀]
  have hb₁ : (SSet.ι₀ ≫ h₀) ≫ p = intervalEndpoint E 1 ≫
      (p ▷ (Δ[1] : SSet.{u}) ≫ H₁.h) := by
    calc
      _ = p ≫ simplexOrderMap (vertexMeet k) := hmeet
      _ = _ := by
        rw [e₁, ← Category.assoc, SSet.ι₀_comp, Category.assoc, H₁.h₀]
  obtain ⟨h₁, h₁start, h₁base⟩ := interval_lift p hp 1 (SSet.ι₀ ≫ h₀)
    (p ▷ (Δ[1] : SSet.{u}) ≫ H₁.h) hb₁
  rw [e₁] at h₁start
  have h₀A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₀.app d (a.val, t) ∈ A.obj d := by
    intro d a t
    change ((h₀ ≫ p).app d (a.val, t)) ∈ (Λ[n, k]).obj d
    rw [h₀base]
    exact simplexMeetToIdentity_mem_horn k d (p.app d a.val) a.property t
  have h₁A : ∀ (d : SimplexCategoryᵒᵖ) (a : A.obj d) (t : (Δ[1] : SSet.{u}).obj d),
      h₁.app d (a.val, t) ∈ A.obj d := by
    intro d a t
    change ((h₁ ≫ p).app d (a.val, t)) ∈ (Λ[n, k]).obj d
    rw [h₁base]
    exact simplexMeetToVertex_mem_horn k d (p.app d a.val) a.property t
  have hfinal : (SSet.ι₁ ≫ h₁) ≫ p = p ≫
      SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm k) := by
    rw [Category.assoc, h₁base, ← Category.assoc, SSet.ι₁_comp, Category.assoc, H₁.h₁]
  have hend : SSet.Subcomplex.range (SSet.ι₁ ≫ h₁) ≤ A := by
    rintro d x ⟨a, rfl⟩
    change ((SSet.ι₁ ≫ h₁) ≫ p).app d a ∈ (Λ[n, k]).obj d
    rw [hfinal]
    exact const_horn_vertex_mem k d (p.app d a)
  exact subcomplex_inclusion_anodyne A h₀ h₁ h₀end h₁start.symm h₀A h₁A hend

/--
概要：Kan fibration に沿う正次元 horn の逆像の包含は局所化で可逆である。
方針：証明済みの anodyne 性に局所化の普遍性を適用する。
規約：Segal 1974 Proposition 1.6 の基底変換の補助。
使われ方：従来の局所化同型の界面を保つ。
-/
theorem horn_preimage_localized_isIso {n : ℕ} [NeZero n] (k : Fin (n + 1))
    {E : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) (hp : SSet.modelCategoryQuillen.J.rlp p) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((Λ[n, k]).preimage p).ι) :=
  Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (horn_preimage_anodyne k p hp)

/--
概要：部分単体集合の逆像は厳密な引き戻しを与える。
方針：各次数で逆像の集合の普遍性を確認する。
規約：射影は包含と fromPreimage を使う。
使われ方：horn の逆像の結果を任意の引き戻し四角形へ移す。
-/
theorem subcomplexPreimage_isPullback {E B : SSet.{u}} (A : B.Subcomplex) (p : E ⟶ B) :
    IsPullback (A.preimage p).ι (A.fromPreimage p) p A.ι := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr
  refine ⟨by rfl, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext h.1
  · intro e a h
    refine ⟨⟨e, ?_⟩, rfl, Subtype.ext h⟩
    change p.app d e ∈ A.obj d
    rw [h]
    exact a.property

/--
概要：正次元 horn の Kan fibration に沿う任意の厳密引き戻しの上辺は局所化同型である。
方針：逆像の標準引き戻しとの一意な同型で比較する。
規約：Segal 1974 Proposition 1.6 の基底変換の補助。
使われ方：スライス圏の積が horn に誘導する射の判定。
-/
theorem pullback_horn_localized_isIso {n : ℕ} [NeZero n] (k : Fin (n + 1))
    {E P : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (i : P ⟶ E) (j : P ⟶ (Λ[n, k] : SSet.{u})) (sq : IsPullback i j p (Λ[n, k]).ι) :
    IsIso (AnodyneHomotopy.anodyneQ.map i) := by
  let e := sq.isoIsPullback _ _ (subcomplexPreimage_isPullback (Λ[n, k]) p)
  have he : e.hom ≫ ((Λ[n, k]).preimage p).ι = i := sq.isoIsPullback_hom_fst ..
  have : IsIso (AnodyneHomotopy.anodyneQ.map ((Λ[n, k]).preimage p).ι) :=
    horn_preimage_localized_isIso k p hp
  rw [← he, Functor.map_comp]
  infer_instance

/--
概要：正次元 horn の Kan fibration に沿う任意の厳密引き戻しの上辺は anodyne である。
方針：逆像の包含との標準同型を合成し、anodyne 性を移す。
規約：Moss arXiv:1506.04887v2 Theorem 5.1 と異なり strong anodyne 性は主張しない。
使われ方：スライスの右随伴の任意の Kan fibration の保存。
-/
theorem pullback_horn_anodyne {n : ℕ} [NeZero n] (k : Fin (n + 1))
    {E P : SSet.{u}} (p : E ⟶ (Δ[n] : SSet.{u})) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (i : P ⟶ E) (j : P ⟶ (Λ[n, k] : SSet.{u})) (sq : IsPullback i j p (Λ[n, k]).ι) :
    SSet.anodyneExtensions i := by
  let e := sq.isoIsPullback _ _ (subcomplexPreimage_isPullback (Λ[n, k]) p)
  have he : e.hom ≫ ((Λ[n, k]).preimage p).ι = i := sq.isoIsPullback_hom_fst ..
  rw [← he]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (horn_preimage_anodyne k p hp)

end SerrePositivity.KST.Comparison
