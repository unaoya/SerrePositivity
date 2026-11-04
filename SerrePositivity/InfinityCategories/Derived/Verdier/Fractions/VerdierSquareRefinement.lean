module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement
public import SerrePositivity.InfinityCategories.Core.SquareHomotopyCategory

/-!
概要：指定商四角形を、同じ実 cospan と弱同値な下辺を持つ元の四角形へ戻す。
方針：四角形を有限 cospan 上の錐に直し、実錐回収の同じ slice 比較を使う。
規約：右辺・上辺は厳密に固定し、比較は四角形全体の関手同型として保持する。
使われ方：有限線型図式の前段分母と次辺族を接続する際の実分母回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定された商四角形を、同じ元の cospan 上の実錐として読む。 -/
def verdierSquareQuotientCone {B C : SSet.{u}} (q : B ⟶ C)
    (R : (horn 2 2 : SSet.{u}) ⟶ B) (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hT : cospanSquareBoundary ≫ T = R ≫ q) : JoinCone (R ≫ q) :=
  ⟨cospanConeSquareIso.hom ≫ T, by
    simpa only [cospanSquareBoundary, Category.assoc] using hT⟩

/-- 同じ実 cospan を保持する錐と、指定商四角形への実 slice 比較辺。 -/
structure VerdierSquareRefinement {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (_h : IsVerdierSequence i q)
    (R : (horn 2 2 : SSet.{u}) ⟶ B.obj)
    (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hT : cospanSquareBoundary ≫ T = R ≫ q.hom) where
  cone : JoinCone R
  comparison : Truncated.Edge (X := (truncation 2).obj (sliceOver (R ≫ q.hom)))
    (mapJoinCone q.hom cone) (verdierSquareQuotientCone q.hom R T hT)
  isInvertible : IsInvertibleEdge (X := sliceOver (R ≫ q.hom)) comparison

namespace VerdierSquareRefinement
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {R : (horn 2 2 : SSet.{u}) ⟶ B.obj}
  {T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj}
  {hT : cospanSquareBoundary ≫ T = R ≫ q.hom}
  (d : VerdierSquareRefinement h R T hT)

/-- 回収した実四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ B.obj :=
  cospanConeSquareIso.inv ≫ d.cone.val

/-- 右辺・上辺を合わせた元の実 cospan は厳密に保存される。 -/
lemma cospan_eq : cospanSquareBoundary ≫ d.square = R := by
  simp only [square, cospanSquareBoundary, Category.assoc, Iso.hom_inv_id_assoc]
  exact d.cone.property

/-- 元の右辺は同じ一次単体族として保存される。 -/
lemma right_eq : squareRightEdge ≫ d.square = horn₂₂.ι₀₂ ≫ R := by
  rw [← cospanSquareBoundary_rightEdge, Category.assoc, d.cospan_eq]

/-- 元の上辺は同じ一次単体族として保存される。 -/
lemma top_eq : squareTopEdge ≫ d.square = horn₂₂.ι₁₂ ≫ R := by
  rw [← cospanSquareBoundary_topEdge, Category.assoc, d.cospan_eq]

/-- 固定 cospan の各頂点への比較は、同じ実 slice 辺の合成二単体を保持する。 -/
def legTriangle (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    Truncated.Edge.CompStruct
      (d.comparison.map ((truncation 2).map (sliceOverProjection (R ≫ q.hom))))
      (F2.nativeConeLeg (verdierSquareQuotientCone q.hom R T hT) k)
      (F2.nativeConeLeg (mapJoinCone q.hom d.cone) k) :=
  coneLegComparisonTriangle d.comparison k

/-- 同じ実 slice 比較辺から回収する、指定商四角形全体への関手同型。 -/
def iso : FunctorIso (d.square ≫ q.hom) T := by
  have hv : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  have e := coneFunctorIsoOfVertexIso (mapJoinCone q.hom d.cone)
    (verdierSquareQuotientCone q.hom R T hT)
    (asIso (Truncated.HomotopyCategory.homMk d.comparison))
  simpa only [square, verdierSquareQuotientCone, mapJoinCone, Category.assoc,
    Iso.inv_hom_id_assoc] using e.precomp cospanConeSquareIso.inv

/-- 指定商四角形の下辺が可逆なら、回収した同じ実下辺は元の弱同値。 -/
lemma bottom_mem (hbottom : IsInvertibleEdge (X := C.obj) (squareBottomArrow T)) :
    (squareBottomArrow d.square).edge ∈ weakEquivalences i := by
  let a := squareBottomArrow (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))
  have hraw (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj) :
      (a.map ((truncation 2).map F)).edge = (squareBottomArrow F).edge := by
    rw [squareBottomArrow_edge]
    change F.app (Opposite.op ⦋1⦌) a.edge = _
    dsimp only [a]
    rw [squareBottomArrow_edge, Category.comp_id, ← SSet.yonedaEquiv_comp]
  have ht : IsInvertibleEdge (X := C.obj) (a.map ((truncation 2).map T)) :=
    (isInvertibleEdge_congr (hraw T)).mpr hbottom
  have hs : IsInvertibleEdge (X := C.obj)
      (a.map ((truncation 2).map (d.square ≫ q.hom))) :=
    (NatIso.isIso_map_iff d.iso.toNatIso
      (Truncated.HomotopyCategory.homMk a)).mpr ht
  apply (mem_weakEquivalences_iff_invertible h (squareBottomArrow d.square)).mpr
  exact (isInvertibleEdge_congr (e :=
    (squareBottomArrow d.square).map ((truncation 2).map q.hom)) rfl).mpr hs

end VerdierSquareRefinement

/-- 任意の指定商四角形を、同じ元の cospan と全 slice 比較辺を持つ実四角形へ回収する。 -/
lemma exists_verdierSquareRefinement {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (R : (horn 2 2 : SSet.{u}) ⟶ B.obj)
    (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hT : cospanSquareBoundary ≫ T = R ≫ q.hom) :
    Nonempty (VerdierSquareRefinement h R T hT) := by
  obtain ⟨c, ⟨e⟩⟩ := exists_verdierQuotientConeIsoRefinement h R
    (verdierSquareQuotientCone q.hom R T hT)
  obtain ⟨v, hv⟩ := homotopyCategory_homMk_surjective
    (X := sliceOver (R ≫ q.hom))
    (mapJoinCone q.hom c) (verdierSquareQuotientCone q.hom R T hT) e.hom
  have hi : IsInvertibleEdge (X := sliceOver (R ≫ q.hom)) v := by
    change IsIso (Truncated.HomotopyCategory.homMk v)
    rw [hv]
    infer_instance
  exact ⟨⟨c, v, hi⟩⟩

end SerrePositivity.KST.LocalizingInvariants
