module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeIso
public import SerrePositivity.InfinityCategories.Core.JoinReverseBoundary
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.PrismOpposite
public import SerrePositivity.InfinityCategories.Stable.FiniteOppositeSSet
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiniteJoin
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：元の有限図式と尾部の貼合せに始点を加えた形を、二つの左錐の積として表す。
方針：既存の任意形状に対する右錐の積の同型を反転し、全包含を保持する。
規約：元の二形状は任意であり、有限性は後の実錐回収にのみ使う。
使われ方：完成側有限境界の次元延長で、元の図式と回収済み尾部を同時に保つ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 反転した右錐を、元の形状の左錐へ戻す標準同型。 -/
def initialConeOppositeIso (K : SSet.{u}) :
    (join K.op (Δ[0] : SSet.{u})).op ≅ join (Δ[0] : SSet.{u}) K :=
  stableJoinReverseIso K.op Δ[0] ≪≫
    joinIso (stdSimplex.opIso ⦋0⦌) (SSet.opFunctorCompOpFunctorIso.app K)

/-- 反転前の元の図式の包含は、同じ左錐の底包含へ戻る。 -/
lemma initialConeOppositeIso_old (K : SSet.{u}) :
    SSet.opFunctor.map (joinInl K.op (Δ[0] : SSet.{u})) ≫
      (initialConeOppositeIso K).hom =
      (SSet.opFunctorCompOpFunctorIso.app K).hom ≫ joinInr (Δ[0] : SSet.{u}) K := by
  rw [initialConeOppositeIso, Iso.trans_hom, ← Category.assoc, stableJoinReverse_inl]
  exact joinInr_joinMap _ _

/-- 元の図式と尾部を貼った、共通始点を追加する前の全台。 -/
abbrev initialConeTensorCorner (A L : SSet.{u}) : SSet.{u} :=
  (F2.Ind.coneTensorCorner A.op L.op).op

/-- 共通始点を追加した全台は、元の二つの左錐の積そのもの。 -/
def initialConeTensorIso (A L : SSet.{u}) :
    join (Δ[0] : SSet.{u}) (initialConeTensorCorner A L) ≅
      join (Δ[0] : SSet.{u}) A ⊗ join (Δ[0] : SSet.{u}) L :=
  joinIso (stdSimplex.opIso ⦋0⦌).symm (Iso.refl _) ≪≫
    (stableJoinReverseIso (F2.Ind.coneTensorCorner A.op L.op) Δ[0]).symm ≪≫
    SSet.opFunctor.mapIso (F2.Ind.coneTensorCoconeIso A.op L.op) ≪≫
    (opTensorIso (join A.op Δ[0]) (join L.op Δ[0])).symm ≪≫
    tensorIso (initialConeOppositeIso A) (initialConeOppositeIso L)

/-- 元の図式と尾部を貼った全台を、元の二つの左錐の積へ含める。 -/
def initialConeTensorCornerInclusion (A L : SSet.{u}) : initialConeTensorCorner A L ⟶
    join (Δ[0] : SSet.{u}) A ⊗ join (Δ[0] : SSet.{u}) L :=
  SSet.opFunctor.map (F2.Ind.coneTensorCornerInclusion A.op L.op) ≫
    (opTensorIso (join A.op Δ[0]) (join L.op Δ[0])).inv ≫
      ((initialConeOppositeIso A).hom ⊗ₘ (initialConeOppositeIso L).hom)

lemma initialConeTensorIso_inr (A L : SSet.{u}) :
    joinInr (Δ[0] : SSet.{u}) (initialConeTensorCorner A L) ≫
      (initialConeTensorIso A L).hom = initialConeTensorCornerInclusion A L := by
  simp only [initialConeTensorIso, Iso.trans_hom, joinIso, Iso.symm_hom,
    initialConeTensorCornerInclusion, tensorIso_hom]
  rw [← Category.assoc (joinInr _ _) (joinMap _ _), joinInr_joinMap,
    Iso.refl_hom, Category.id_comp,
    ← Category.assoc (joinInr _ _) (stableJoinReverseIso _ _).inv,
    stableJoinReverse_inr_inv]
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc (SSet.opFunctor.map _) (SSet.opFunctor.map _),
    ← SSet.opFunctor.map_comp]
  change SSet.opFunctor.map (joinInl _ _ ≫ F2.Ind.coneTensorCocone A.op L.op) ≫ _ = _
  rw [F2.Ind.coneTensorCocone_inl]

instance initialConeTensorCorner_finite (A L : SSet.{u}) [A.Finite] [L.Finite] :
    (initialConeTensorCorner A L).Finite := by
  have : (F2.Ind.coneTensorCorner A.op L.op).Finite := by
    apply SSet.finite_of_isColimit (pushoutIsPushout
      (A.op ◁ joinInl L.op (Δ[0] : SSet.{u})) (joinInl A.op Δ[0] ▷ L.op))
    rintro (_ | (_ | _)) <;> simp only [span_left, span_right, span_zero] <;> infer_instance
  infer_instance

instance initialConeTensorCornerInclusion_mono (A L : SSet.{u}) :
    Mono (initialConeTensorCornerInclusion A L) := by
  rw [← initialConeTensorIso_inr]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants
