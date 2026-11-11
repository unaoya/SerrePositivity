module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeShape
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceOrderMap

/-! # necklace の実単体集合の連結包含と射影
概要：有限 joints の連結を、元の全高次単体上の射に持ち上げる。
方針：bead 条件を保つ番号の包含と切り詰めを使う。
規約：共有する終始点を厳密に保持する。使われ方：wedge の普遍性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

open CategoryTheory _root_.Simplicial SSet

/-- 連結後の実単体集合への左包含。 -/
def wedgeInl (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.carrier.{u} ⟶ (T.wedge U).carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap (T.wedgeLeftVertex U) (T.wedge_allows_left U)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInl)


/-- 連結後の実単体集合への右包含。 -/
def wedgeInr (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : U.carrier.{u} ⟶ (T.wedge U).carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap (T.wedgeRightVertex U) (T.wedge_allows_right U)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInr)


/-- 元の左 necklace への単体的な切り詰め。 -/
def wedgeFst (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.wedge U).carrier.{u} ⟶ T.carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap (T.wedgeLeftClamp U) (T.wedge_allows_leftClamp U)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeFst)


/-- 元の右 necklace への単体的な切り詰め。 -/
def wedgeSnd (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : (T.wedge U).carrier.{u} ⟶ U.carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap (T.wedgeRightClamp U) (T.wedge_allows_rightClamp U)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeSnd)


/-- 左包含と左射影の合成は全単体で恒等。 -/
lemma wedgeInl_fst (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.wedgeInl U ≫ T.wedgeFst U = 𝟙 T.carrier.{u} := by
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInl_fst)


/-- 右包含と右射影の合成は全単体で恒等。 -/
lemma wedgeInr_snd (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.wedgeInr U ≫ T.wedgeSnd U = 𝟙 U.carrier.{u} := by
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInr_snd)


/-- 左側にある元の単体は、左射影と左包含で厳密に回収される。 -/
lemma wedge_left_recover (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) (h : ∀ i, (s.val i).val ≤ T.vertexMax) :
    (T.wedgeInl U).app _ ((T.wedgeFst U).app _ s) = s := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change min (s.val i).val T.vertexMax = (s.val i).val
  exact min_eq_left (h i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_left_recover)


/-- 右側にある元の単体は、右射影と右包含で厳密に回収される。 -/
lemma wedge_right_recover (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) (h : ∀ i, T.vertexMax ≤ (s.val i).val) :
    (T.wedgeInr U).app _ ((T.wedgeSnd U).app _ s) = s := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change T.vertexMax + ((s.val i).val - T.vertexMax) = (s.val i).val
  have := h i
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_right_recover)


/-- 元の左包含と右包含は、連結後の全単体を覆う。 -/
lemma wedge_simplex_cover (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : (T.wedge U).carrier.{u} _⦋n⦌) :
    (∃ t, (T.wedgeInl U).app _ t = s) ∨ (∃ t, (T.wedgeInr U).app _ t = s) := by
  rcases T.wedge_allows_split U s.property with h | h
  · exact Or.inl ⟨_, T.wedge_left_recover U s h⟩
  · exact Or.inr ⟨_, T.wedge_right_recover U s h⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_simplex_cover)


/-- 連結からの元の単体的射は、左右の元の包含への制限で決まる。 -/
lemma wedge_hom_ext (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {K : SSet.{u}}
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_hom_ext)


/-- 元の一点から指定の頂点への定値な単体的写像。 -/
def pointMap (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0).carrier.{u} ⟶ T.carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap (OrderHom.const _ v) (by intro n s hs; exact T.allows_const v n)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (pointMap)


/-- 一点からの射は全単体で元の定値単体を与える。 -/
lemma pointMap_app (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (v : T.Vertex) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0).carrier.{u} _⦋n⦌) :
    (T.pointMap v).app _ s = T.constantSimplex v n := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (pointMap_app)


/-- 共有する元の終始点から連結への二つの射は全単体で一致する。 -/
lemma wedge_seam (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_seam)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap_app := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_app

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeFst (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeFst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeFst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl_fst := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_fst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr_snd := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_snd

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeSnd (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeSnd := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeSnd

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_hom_ext := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_hom_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_left_recover := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_left_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_right_recover := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_right_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_seam := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_seam

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_simplex_cover := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_simplex_cover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.pointMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap._proof_1
