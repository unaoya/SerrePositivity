module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomElements
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates

/-!
概要：edgewise の長い射列から、同じ両端間の射の列を Hom の元の圏に読み戻す。
方針：既存の左・右頂点を対にし、元の射列の合成則を可換四角形の条件に使う。
規約：各対角の射を保持し、始点だけから存在を選ばない。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の Hom 模型比較の逆向き。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 同じ添字の左頂点は右頂点に先行する。
Kerodon Proposition 8.1.1.10（Tag 03JN）、長い射列の交差射の添字の法則。 -/
lemma homLong_cross_le (i : Fin (n + 1)) :
    edgewiseLeftVertex n i ≤ edgewiseRightVertex n i := by
  change n - i.val ≤ n + 1 + i.val
  omega

/-- 長い射列の同じ左・右添字を結ぶ射を、Hom の元として読む。
Kerodon Proposition 8.1.1.10（Tag 03JN）、既存の長い単体模型の対象の読み戻し。 -/
def ordinaryHomFromLongObj (L : ComposableArrows C (n + n + 1))
    (i : Fin (n + 1)) : OrdinaryHomElements C :=
  Functor.elementsMk _ (Opposite.op (L.obj (edgewiseLeftVertex n i)),
    L.obj (edgewiseRightVertex n i))
    (L.map (homOfLE (homLong_cross_le i)))

/-- 添字を増やすと左側だけは逆向きに進む。
Kerodon Proposition 8.1.1.10（Tag 03JN）、指定左頂点の順序の法則。 -/
lemma homLong_left_le {i j : Fin (n + 1)} (h : i ≤ j) :
    edgewiseLeftVertex n j ≤ edgewiseLeftVertex n i := by
  change n - j.val ≤ n - i.val
  omega

/-- 添字を増やすと右側は順向きに進む。
Kerodon Proposition 8.1.1.10（Tag 03JN）、指定右頂点の順序の法則。 -/
lemma homLong_right_le {i j : Fin (n + 1)} (h : i ≤ j) :
    edgewiseRightVertex n i ≤ edgewiseRightVertex n j := by
  change n + 1 + i.val ≤ n + 1 + j.val
  omega

/-- 長い射列の合成則は、元の Hom の元の圏の可換四角形を与える。
Kerodon Proposition 8.1.1.10（Tag 03JN）、逆向きの射の指定写像。 -/
def ordinaryHomFromLongMap (L : ComposableArrows C (n + n + 1))
    {i j : Fin (n + 1)} (h : i ≤ j) :
    ordinaryHomFromLongObj L i ⟶ ordinaryHomFromLongObj L j where
  hom := ((L.map (homOfLE (homLong_left_le h))).op,
    L.map (homOfLE (homLong_right_le h)))
  map_val := by
    change (L.map (homOfLE (homLong_left_le h)) ≫
      L.map (homOfLE (homLong_cross_le i))) ≫
      L.map (homOfLE (homLong_right_le h)) = L.map (homOfLE (homLong_cross_le j))
    rw [← L.map_comp, ← L.map_comp]
    congr 1

private lemma longMap_id (L : ComposableArrows C (n + n + 1))
    (i : Fin (n + n + 1 + 1)) (h : i ≤ i) : L.map (homOfLE h) = 𝟙 (L.obj i) := by
  have he : homOfLE h = 𝟙 i := Subsingleton.elim _ _
  rw [he, L.map_id]

private lemma longMap_comp (L : ComposableArrows C (n + n + 1))
    {i j k : Fin (n + n + 1 + 1)} (h : i ≤ j) (h' : j ≤ k) (h'' : i ≤ k) :
    L.map (homOfLE h'') = L.map (homOfLE h) ≫ L.map (homOfLE h') := by
  rw [← L.map_comp]
  congr 1

/-- 同じ添字での読み戻しは恒等射を保つ。
Kerodon Proposition 8.1.1.10（Tag 03JN）、長い射列からの復元の単位則。 -/
lemma ordinaryHomFromLongMap_id (L : ComposableArrows C (n + n + 1))
    (i : Fin (n + 1)) :
    ordinaryHomFromLongMap L (le_refl i) = 𝟙 (ordinaryHomFromLongObj L i) := by
  apply Functor.Elements.hom_ext
  apply _root_.Prod.ext
  · change (L.map (homOfLE _)).op = (𝟙 _).op
    rw [longMap_id]
  · change L.map (homOfLE _) = 𝟙 _
    exact longMap_id _ _ _

/-- 読み戻した射の合成は元の長い射列の合成である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、長い射列からの復元の合成則。 -/
lemma ordinaryHomFromLongMap_comp (L : ComposableArrows C (n + n + 1))
    {i j k : Fin (n + 1)} (h : i ≤ j) (h' : j ≤ k) :
    ordinaryHomFromLongMap L (h.trans h') =
      ordinaryHomFromLongMap L h ≫ ordinaryHomFromLongMap L h' := by
  apply Functor.Elements.hom_ext
  apply _root_.Prod.ext
  · change (L.map (homOfLE _)).op =
      (L.map (homOfLE (homLong_left_le h))).op ≫
        (L.map (homOfLE (homLong_left_le h'))).op
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (longMap_comp L _ _ _)
  · change L.map (homOfLE _) =
      L.map (homOfLE (homLong_right_le h)) ≫ L.map (homOfLE (homLong_right_le h'))
    exact longMap_comp L _ _ _

/-- 長い単体の全射列を Hom の元の圏の全射列として読み戻す。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ各対角の射を持つ逆向きの模型比較。 -/
def ordinaryHomFromLongChain (L : ComposableArrows C (n + n + 1)) :
    ComposableArrows (OrdinaryHomElements C) n where
  obj := ordinaryHomFromLongObj L
  map h := ordinaryHomFromLongMap L (leOfHom h)
  map_id i := ordinaryHomFromLongMap_id L i
  map_comp h h' := ordinaryHomFromLongMap_comp L (leOfHom h) (leOfHom h')

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
