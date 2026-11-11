module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentSimplexData

/-!
# dg 単体の有限頂点番号と coherent 内部座標

概要：Fin の頂点集合を ULift の native な座標へ移し、削除・切断・内部点の和を比較する。
方針：ULift の単射な像と開区間への制限を使う。
規約：頂点とその順序は変えず、宇宙だけを持ち上げる。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の既存 dg nerve の rhs への移送。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：有限頂点集合を native な ULift の頂点集合へ移す。
方針：ULift.up の単射な像を取る。
規約：native な Hom の宇宙を u に保つ。
使われ方：Kerodon 2.5.9（Tag 00SC） の有限単体の内部立方体の台集合。 -/
def coherentVertexSet {n : ℕ} (I : Finset (Fin (n + 1))) :
    Finset (ULift.{u} (Fin (n + 1))) := I.image ULift.up

/-- 概要：有限頂点番号から両端の間の native な内部座標を取り出す。
方針：ULift の像の開区間への制限を取る。
規約：両端は内部座標に数えない。
使われ方：HA 1.3.1.16 の dg 単体の各成分の座標集合。 -/
def coherentVertexInterior {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    Finset (Set.Ioo (ULift.up a : ULift.{u} (Fin (n + 1))) (ULift.up b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet (coherentVertexSet I) (ULift.up a) (ULift.up b)

/-- 概要：頂点を持ち上げても濃度は変わらない。
方針：ULift.up の単射性を使う。
規約：Finset の濃度の等式。
使われ方：Kerodon 2.5.9（Tag 00SC） の次数の表示の同定。 -/
lemma coherentVertexSet_card {n : ℕ} (I : Finset (Fin (n + 1))) :
    (coherentVertexSet.{u} I).card = I.card :=
  Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg ULift.down h)

/-- 概要：頂点の持ち上げは一点削除と可換である。
方針：単射な像と erase の可換性を使う。
規約：削除する頂点も持ち上げる。
使われ方：HA 1.3.1.16 の削除成分の座標集合の同定。 -/
lemma coherentVertexSet_erase {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    coherentVertexSet.{u} (I.erase j) = (coherentVertexSet I).erase (ULift.up j) := by
  exact Finset.image_erase (fun _ _ h ↦ congrArg ULift.down h) I j

/-- 概要：頂点の持ち上げは切断点以下への制限と可換である。
方針：像の filter を元の集合の filter へ移す。
規約：順序は持ち上げ前後で同じ。
使われ方：Kerodon 2.5.9（Tag 00SC） の前半の成分の座標集合の同定。 -/
lemma coherentVertexSet_left {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    coherentVertexSet.{u} (I.filter (· ≤ j)) = (coherentVertexSet I).filter (· ≤ ULift.up j) := by
  symm
  exact Finset.filter_image

/-- 概要：頂点の持ち上げは切断点以上への制限と可換である。
方針：像の filter を元の集合の filter へ移す。
規約：順序は持ち上げ前後で同じ。
使われ方：Kerodon 2.5.9（Tag 00SC） の後半の成分の座標集合の同定。 -/
lemma coherentVertexSet_right {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    coherentVertexSet.{u} (I.filter (j ≤ ·)) = (coherentVertexSet I).filter (ULift.up j ≤ ·) := by
  symm
  exact Finset.filter_image

/-- 概要：最小頂点は持ち上げ後も最小である。
方針：像の元を元の頂点に戻して下界性を使う。
規約：最小元の所属も保存する。
使われ方：HA 1.3.1.16 の内部点数と全頂点数の比較。 -/
lemma coherentVertexSet_isLeast {n : ℕ} {I : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (ha : IsLeast (I : Set (Fin (n + 1))) a) :
    IsLeast ((coherentVertexSet.{u} I) : Set _) (ULift.up a) := by
  refine ⟨Finset.mem_image.mpr ⟨a, ha.1, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  exact ha.2 ht

/-- 概要：最大頂点は持ち上げ後も最大である。
方針：像の元を元の頂点に戻して上界性を使う。
規約：最大元の所属も保存する。
使われ方：HA 1.3.1.16 の符号の指数の点数の比較。 -/
lemma coherentVertexSet_isGreatest {n : ℕ} {I : Finset (Fin (n + 1))} {b : Fin (n + 1)}
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    IsGreatest ((coherentVertexSet.{u} I) : Set _) (ULift.up b) := by
  refine ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  exact hb.2 ht

/-- 概要：native な内部座標の数に二を足すと全頂点数となる。
方針：持ち上げた最小・最大元を使って内部点数を計算する。
規約：異なる両端を仮定する。
使われ方：Kerodon 2.5.9（Tag 00SC） の次数 2−|I| と負の内部点数の同定。 -/
lemma coherentVertexInterior_card {n : ℕ} {I : Finset (Fin (n + 1))} {a b : Fin (n + 1)}
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hab : a < b) : (coherentVertexInterior.{u} I a b).card + 2 = I.card := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_coherentInteriorSet (coherentVertexSet_isLeast ha)
    (coherentVertexSet_isGreatest hb) hab).trans (coherentVertexSet_card I)

/-- 概要：native な内部座標の削除は元の頂点の削除に等しい。
方針：持ち上げと erase の可換性の後に内部集合の erase の式を使う。
規約：削除点は両端の間にある。
使われ方：HA 1.3.1.16 の dg 単体の削除成分。 -/
lemma coherentVertexInterior_erase {n : ℕ} (I : Finset (Fin (n + 1)))
    {a b j : Fin (n + 1)} (haj : a < j) (hjb : j < b) :
    coherentVertexInterior.{u} (I.erase j) a b =
      (coherentVertexInterior I a b).erase ⟨ULift.up j, haj, hjb⟩ := by
  unfold coherentVertexInterior
  rw [coherentVertexSet_erase]
  ext t
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet, Finset.mem_erase]
  constructor
  · rintro ⟨hne, hm⟩
    exact ⟨fun h ↦ hne (congrArg Subtype.val h), hm⟩
  · rintro ⟨hne, hm⟩
    exact ⟨fun h ↦ hne (Subtype.ext h), hm⟩

/-- 概要：前半の頂点集合の内部座標は元の内部集合を前半へ制限したものに等しい。
方針：頂点の切断と内部区間への制限を比較する。
規約：切断点は元の両端の間にある。
使われ方：Kerodon 2.5.9（Tag 00SC） の前半の dg 成分と合成面の対応。 -/
lemma coherentVertexInterior_left {n : ℕ} (I : Finset (Fin (n + 1)))
    {a b j : Fin (n + 1)} (_haj : a < j) (hjb : j < b) :
    coherentVertexInterior.{u} (I.filter (· ≤ j)) a j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet (coherentVertexInterior I a b) (ULift.up a) (ULift.up j) := by
  unfold coherentVertexInterior
  rw [coherentVertexSet_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet_coherentInterior le_rfl (show ULift.up j ≤ ULift.up b from hjb.le)]

/-- 概要：後半の頂点集合の内部座標は元の内部集合を後半へ制限したものに等しい。
方針：頂点の切断と内部区間への制限を比較する。
規約：切断点は元の両端の間にある。
使われ方：Kerodon 2.5.9（Tag 00SC） の後半の dg 成分と合成面の対応。 -/
lemma coherentVertexInterior_right {n : ℕ} (I : Finset (Fin (n + 1)))
    {a b j : Fin (n + 1)} (haj : a < j) (_hjb : j < b) :
    coherentVertexInterior.{u} (I.filter (j ≤ ·)) j b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet (coherentVertexInterior I a b) (ULift.up j) (ULift.up b) := by
  unfold coherentVertexInterior
  rw [coherentVertexSet_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet_coherentInterior (show ULift.up a ≤ ULift.up j from haj.le) le_rfl]

/-- 概要：頂点の持ち上げは指定点より大きい頂点の個数を保つ。
方針：単射な順序写像の像の符号の指数の濃度の式を使う。
規約：指定点は元の集合に属する。
使われ方：HA 1.3.1.16 の dg nerve の符号を native な座標へ移す。 -/
lemma coherentVertexSet_sign_card {n : ℕ} (I : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∈ I) :
    ((coherentVertexSet.{u} I).filter (ULift.up j < ·)).card = (I.filter (j < ·)).card := by
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_sign_card
    (f := (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))) (fun _ _ h ↦ h)
    (fun _ _ _ _ h ↦ congrArg ULift.down h) hj using 1
  congr 1
  ext x
  simp only [coherentVertexSet, Finset.mem_filter, Finset.mem_image]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
