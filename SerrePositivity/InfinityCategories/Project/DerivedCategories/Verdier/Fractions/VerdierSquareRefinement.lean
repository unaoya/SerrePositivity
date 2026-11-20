module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierSquareRefinement
end SerrePositivity.KST.LocalizingInvariants.VerdierSquareRefinement
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 指定された商四角形を、同じ元の cospan 上の実錐として読む。 -/
def verdierSquareQuotientCone {B C : SSet.{u}} (q : B ⟶ C)
    (R : (horn 2 2 : SSet.{u}) ⟶ B) (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ T = R ≫ q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (R ≫ q) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ T, by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc] using hT⟩

/-- 同じ実 cospan を保持する錐と、指定商四角形への実 slice 比較辺。 -/
structure VerdierSquareRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (_h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (R : (horn 2 2 : SSet.{u}) ⟶ B.obj)
    (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ T = R ≫ q.hom) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone R
  comparison : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (R ≫ q.hom)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom cone) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone q.hom R T hT)
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (R ≫ q.hom)) comparison

namespace VerdierSquareRefinement

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {R : (horn 2 2 : SSet.{u}) ⟶ B.obj}
  {T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj}
  {hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ T = R ≫ q.hom}
  (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSquareRefinement h R T hT)

/-- 回収した実四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ B.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ d.cone.val

/-- 右辺・上辺を合わせた元の実 cospan は厳密に保存される。 -/
lemma cospan_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ d.square = R := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSquareRefinement.square, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id_assoc]
  exact d.cone.property

/-- 元の右辺は同じ一次単体族として保存される。 -/
lemma right_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.square = horn₂₂.ι₀₂ ≫ R := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, Category.assoc, d.cospan_eq]

/-- 元の上辺は同じ一次単体族として保存される。 -/
lemma top_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.square = horn₂₂.ι₁₂ ≫ R := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, Category.assoc, d.cospan_eq]

/-- 固定 cospan の各頂点への比較は、同じ実 slice 辺の合成二単体を保持する。 -/
def legTriangle (k : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    Truncated.Edge.CompStruct
      (d.comparison.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (R ≫ q.hom))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone q.hom R T hT) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d.cone) k) :=
  coneLegComparisonTriangle d.comparison k

/-- 同じ実 slice 比較辺から回収する、指定商四角形全体への関手同型。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ q.hom) T := by
  have hv : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d.cone)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone q.hom R T hT)
    (asIso (Truncated.HomotopyCategory.homMk d.comparison))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSquareRefinement.square, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone, Category.assoc,
    Iso.inv_hom_id_assoc] using e.precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv

/-- 指定商四角形の下辺が可逆なら、回収した同じ実下辺は元の弱同値。 -/
lemma bottom_mem (hbottom : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow T)) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow d.square).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  let a := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u}))
  have hraw (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj) :
      (a.map ((truncation 2).map F)).edge = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow F).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge]
    change F.app (Opposite.op ⦋1⦌) a.edge = _
    dsimp only [a]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge, Category.comp_id, ← SSet.yonedaEquiv_comp]
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) (a.map ((truncation 2).map T)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (hraw T)).mpr hbottom
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj)
      (a.map ((truncation 2).map (d.square ≫ q.hom))) :=
    (NatIso.isIso_map_iff d.iso.toNatIso
      (Truncated.HomotopyCategory.homMk a)).mpr ht
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow d.square)).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow d.square).map ((truncation 2).map q.hom)) rfl).mpr hs

end VerdierSquareRefinement

/-- 任意の指定商四角形を、同じ元の cospan と全 slice 比較辺を持つ実四角形へ回収する。 -/
lemma exists_verdierSquareRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (R : (horn 2 2 : SSet.{u}) ⟶ B.obj)
    (T : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C.obj)
    (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ T = R ≫ q.hom) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSquareRefinement h R T hT) := by
  obtain ⟨c, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone q.hom R T hT)
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (R ≫ q.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSquareQuotientCone q.hom R T hT) e.hom
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (R ≫ q.hom)) v := by
    change IsIso (Truncated.HomotopyCategory.homMk v)
    rw [hv]
    infer_instance
  exact ⟨⟨c, v, hi⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
