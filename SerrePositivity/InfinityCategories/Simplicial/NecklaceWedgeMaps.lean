module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeShape
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceOrderMap

/-! # necklace の実単体集合の連結包含と射影
概要：有限 joints の連結を、元の全高次単体上の射に持ち上げる。
方針：bead 条件を保つ番号の包含と切り詰めを使う。
規約：共有する終始点を厳密に保持する。使われ方：wedge の普遍性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open SerrePositivity.KST.SConstruction.NecklaceShape
open CategoryTheory _root_.Simplicial SSet

/-- 連結後の実単体集合への左包含。 -/
def wedgeInl (T U : NecklaceShape) : T.carrier.{u} ⟶ (T.wedge U).carrier.{u} :=
  orderMap (T.wedgeLeftVertex U) (T.wedge_allows_left U)

/-- 連結後の実単体集合への右包含。 -/
def wedgeInr (T U : NecklaceShape) : U.carrier.{u} ⟶ (T.wedge U).carrier.{u} :=
  orderMap (T.wedgeRightVertex U) (T.wedge_allows_right U)

/-- 元の左 necklace への単体的な切り詰め。 -/
def wedgeFst (T U : NecklaceShape) : (T.wedge U).carrier.{u} ⟶ T.carrier.{u} :=
  orderMap (T.wedgeLeftClamp U) (T.wedge_allows_leftClamp U)

/-- 元の右 necklace への単体的な切り詰め。 -/
def wedgeSnd (T U : NecklaceShape) : (T.wedge U).carrier.{u} ⟶ U.carrier.{u} :=
  orderMap (T.wedgeRightClamp U) (T.wedge_allows_rightClamp U)

/-- 左包含と左射影の合成は全単体で恒等。 -/
lemma wedgeInl_fst (T U : NecklaceShape) : T.wedgeInl U ≫ T.wedgeFst U = 𝟙 T.carrier.{u} := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change min (s.val i).val T.vertexMax = (s.val i).val
  exact min_eq_left (by have := (s.val i).isLt; omega)

/-- 右包含と右射影の合成は全単体で恒等。 -/
lemma wedgeInr_snd (T U : NecklaceShape) : T.wedgeInr U ≫ T.wedgeSnd U = 𝟙 U.carrier.{u} := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change T.vertexMax + (s.val i).val - T.vertexMax = (s.val i).val
  omega

/-- 左側にある元の単体は、左射影と左包含で厳密に回収される。 -/
lemma wedge_left_recover (T U : NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) (h : ∀ i, (s.val i).val ≤ T.vertexMax) :
    (T.wedgeInl U).app _ ((T.wedgeFst U).app _ s) = s := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change min (s.val i).val T.vertexMax = (s.val i).val
  exact min_eq_left (h i)

/-- 右側にある元の単体は、右射影と右包含で厳密に回収される。 -/
lemma wedge_right_recover (T U : NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) (h : ∀ i, T.vertexMax ≤ (s.val i).val) :
    (T.wedgeInr U).app _ ((T.wedgeSnd U).app _ s) = s := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change T.vertexMax + ((s.val i).val - T.vertexMax) = (s.val i).val
  have := h i
  omega

/-- 元の左包含と右包含は、連結後の全単体を覆う。 -/
lemma wedge_simplex_cover (T U : NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) :
    (∃ t, (T.wedgeInl U).app _ t = s) ∨ (∃ t, (T.wedgeInr U).app _ t = s) := by
  rcases T.wedge_allows_split U s.property with h | h
  · exact Or.inl ⟨_, T.wedge_left_recover U s h⟩
  · exact Or.inr ⟨_, T.wedge_right_recover U s h⟩

/-- 連結からの元の単体的射は、左右の元の包含への制限で決まる。 -/
lemma wedge_hom_ext (T U : NecklaceShape) {K : SSet.{u}}
    {f g : (T.wedge U).carrier.{u} ⟶ K}
    (hl : T.wedgeInl U ≫ f = T.wedgeInl U ≫ g)
    (hr : T.wedgeInr U ≫ f = T.wedgeInr U ≫ g) : f = g := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  rcases T.wedge_simplex_cover U s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hl _) t
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app hr _) t

/-- 元の一点から指定の頂点への定値な単体的写像。 -/
def pointMap (T : NecklaceShape) (v : T.Vertex) : (single 0).carrier.{u} ⟶ T.carrier.{u} :=
  orderMap (OrderHom.const _ v) (by intro n s hs; exact T.allows_const v n)

/-- 一点からの射は全単体で元の定値単体を与える。 -/
lemma pointMap_app (T : NecklaceShape) (v : T.Vertex) {n : ℕ}
    (s : (single 0).carrier.{u} _⦋n⦌) :
    (T.pointMap v).app _ s = T.constantSimplex v n := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

/-- 共有する元の終始点から連結への二つの射は全単体で一致する。 -/
lemma wedge_seam (T U : NecklaceShape) :
    T.pointMap.{u} T.last ≫ T.wedgeInl U = U.pointMap U.first ≫ T.wedgeInr U := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change T.vertexMax = T.vertexMax + 0
  omega

end SerrePositivity.InfinityCategories.Simplicial.NecklaceShape

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.pointMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.pointMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap_app := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.pointMap_app

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeFst (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeFst := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeFst

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInl (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl_fst := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInl_fst

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInr (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr_snd := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeInr_snd

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeSnd (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeSnd := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedgeSnd

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_hom_ext := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedge_hom_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_left_recover := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedge_left_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_right_recover := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedge_right_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_seam := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedge_seam

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_simplex_cover := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.wedge_simplex_cover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.pointMap._proof_1
