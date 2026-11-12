module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentCubeDifferential
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex

/-!
# 有限頂点集合と内部点の座標

概要：両端を持つ有限頂点集合から立方体の有限内部座標を作り、濃度と切断を比較する。
方針：開区間の部分型へ制限し、両端の削除と同定して濃度を数える。
規約：dg 単体の次数 2−|I| は内部点数の負に等しい。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の coherent 成分を dg 単体の成分族へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J : Type u} [LinearOrder J]

/-- 概要：有限頂点集合の開区間内の点を立方体の有限座標にする。
方針：有限集合を開区間の部分型へ制限する。
規約：両端点を内部点として数えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 単体の成分の立方体。 -/
def coherentInteriorSet (I : Finset J) (a b : J) : Finset (Set.Ioo a b) :=
  I.subtype (fun t ↦ t ∈ Set.Ioo a b)

/-- 概要：内部座標への所属は元の頂点集合への所属である。
方針：開区間の条件は部分型に含まれている。
規約：点は既に開区間内にある。
使われ方：HA 1.3.1.16 の有限頂点集合の成分計算。 -/
lemma mem_coherentInteriorSet (I : Finset J) (a b : J) (t : Set.Ioo a b) :
    t ∈ coherentInteriorSet I a b ↔ t.val ∈ I := Finset.mem_subtype

/-- 概要：異なる最小・最大の両端を持つ集合の内部点数に二を足すと全頂点数となる。
方針：内部点を両端を削除した集合と同定し、二回の削除の濃度を数える。
規約：両端の間に点がない場合も含む。
使われ方：HA 1.3.1.16 の cochain 次数の同定。 -/
lemma card_coherentInteriorSet {I : Finset J} {a b : J}
    (ha : IsLeast (I : Set J) a) (hb : IsGreatest (I : Set J) b) (hab : a < b) :
    (coherentInteriorSet I a b).card + 2 = I.card := by
  rw [coherentInteriorSet, Finset.card_subtype]
  have h : I.filter (fun t ↦ t ∈ Set.Ioo a b) = (I.erase a).erase b := by
    ext x
    simp only [Finset.mem_filter, Set.mem_Ioo, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hax, hxb⟩
      exact ⟨ne_of_lt hxb, ne_of_gt hax, hx⟩
    · rintro ⟨hxb, hxa, hx⟩
      exact ⟨hx, lt_of_le_of_ne (ha.2 hx) (Ne.symm hxa), lt_of_le_of_ne (hb.2 hx) hxb⟩
  rw [h]
  have h₁ := Finset.card_erase_add_one ha.1
  have h₂ := Finset.card_erase_add_one
    (Finset.mem_erase.mpr ⟨ne_of_gt hab, hb.1⟩ : b ∈ I.erase a)
  omega

/-- 概要：内部点を元の頂点集合から削除する操作は内部座標の一点削除に等しい。
方針：部分型と erase の所属条件を比較する。
規約：両端は変えない。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 方程式の削除成分の内部座標。 -/
lemma coherentInteriorSet_erase (I : Finset J) {a b : J} (j : Set.Ioo a b) :
    coherentInteriorSet (I.erase j.val) a b = (coherentInteriorSet I a b).erase j := by
  ext t
  simp only [mem_coherentInteriorSet, Finset.mem_erase]
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

/-- 概要：内部座標のより小さい区間への制限は元の頂点集合をその区間へ制限したものに等しい。
方針：新しい区間の点は元の区間の点であることから、有限集合の像の所属を比較する。
規約：a≤c、d≤b の下で開区間 c,d を扱う。
使われ方：HA 1.3.1.16 の左右の切断成分の内部座標の同定。 -/
lemma pathIntervalSet_coherentInterior {I : Finset J} {a b c d : J}
    (hac : a ≤ c) (hdb : d ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet (coherentInteriorSet I a b) c d = coherentInteriorSet I c d := by
  ext z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_pathIntervalSet, mem_coherentInteriorSet]
  constructor
  · intro hz
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hz
    have ht' := (mem_coherentInteriorSet I a b t).mp ht
    rwa [he] at ht'
  · intro hz
    refine Finset.mem_image.mpr ⟨⟨z.val, ⟨lt_of_le_of_lt hac z.property.1,
      lt_of_lt_of_le z.property.2 hdb⟩⟩, ?_, rfl⟩
    exact (mem_coherentInteriorSet I a b _).mpr hz

/-- 概要：切断点以下の頂点集合の内部点は元の集合の同じ開区間の内部点である。
方針：開区間内の点は切断点より小さいので filter の条件を既に満たす。
規約：切断点自身は内部点から除かれる。
使われ方：Kerodon 2.5.9（Tag 00SC） の前半の成分の有限座標。 -/
lemma coherentInteriorSet_left (I : Finset J) (a j : J) :
    coherentInteriorSet (I.filter (· ≤ j)) a j = coherentInteriorSet I a j := by
  ext t
  simp [mem_coherentInteriorSet, t.property.2.le]

/-- 概要：切断点以上の頂点集合の内部点は元の集合の同じ開区間の内部点である。
方針：開区間内の点は切断点より大きいので filter の条件を既に満たす。
規約：切断点自身は内部点から除かれる。
使われ方：Kerodon 2.5.9（Tag 00SC） の後半の成分の有限座標。 -/
lemma coherentInteriorSet_right (I : Finset J) (j b : J) :
    coherentInteriorSet (I.filter (j ≤ ·)) j b = coherentInteriorSet I j b := by
  ext t
  simp [mem_coherentInteriorSet, t.property.1.le]

/-- 概要：内部点より大きい全頂点数は、その点より大きい内部点数に終点の一を加えたものである。
方針：大きい内部点の像を、大きい頂点集合から終点を削除した集合と同定する。
規約：始点は既に指定した内部点より小さい。
使われ方：HA 1.3.1.16 の立方体境界と dg nerve の符号の指数の比較。 -/
lemma coherentInterior_larger_card {I : Finset J} {a b : J}
    (hb : IsGreatest (I : Set J) b) (j : Set.Ioo a b) :
    (I.filter (j.val < ·)).card = ((coherentInteriorSet I a b).filter (j < ·)).card + 1 := by
  have hImage : ((coherentInteriorSet I a b).filter (j < ·)).image Subtype.val =
      (I.filter (j.val < ·)).erase b := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, mem_coherentInteriorSet, Finset.mem_erase]
    constructor
    · rintro ⟨t, ⟨ht, hjt⟩, rfl⟩
      exact ⟨ne_of_lt t.property.2, ht, hjt⟩
    · rintro ⟨hxb, hx, hjx⟩
      have hax : a < x := j.property.1.trans hjx
      have hxb' : x < b := lt_of_le_of_ne (hb.2 hx) hxb
      exact ⟨⟨x, hax, hxb'⟩, ⟨hx, hjx⟩, rfl⟩
  have hcard := Finset.card_image_of_injective
    ((coherentInteriorSet I a b).filter (j < ·)) Subtype.val_injective
  rw [hImage] at hcard
  have hc := Finset.card_erase_add_one
    (Finset.mem_filter.mpr ⟨hb.1, j.property.2⟩ : b ∈ I.filter (j.val < ·))
  omega

/-- 概要：dg nerve の符号付きの削除−合成は内部点境界の符号付きの合成−削除に等しい。
方針：指数の終点の一を負号にし、差の順序を入れ替える。
規約：任意の可換加法群で成立する係数の等式。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体微分公式を dg 単体の方程式へ直す。 -/
lemma coherentInterior_term_sign {I : Finset J} {a b : J}
    (hb : IsGreatest (I : Set J) b) (j : Set.Ioo a b)
    {M : Type*} [AddCommGroup M] (f g : M) :
    ((I.filter (j.val < ·)).card : ℤ).negOnePow • (f - g) =
      (-1 : ℤ) ^ ((coherentInteriorSet I a b).filter (j < ·)).card • (g - f) := by
  rw [Units.smul_def, Int.coe_negOnePow_natCast, coherentInterior_larger_card hb j,
    pow_succ, mul_neg_one, neg_smul]
  simp only [smul_sub]
  abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
