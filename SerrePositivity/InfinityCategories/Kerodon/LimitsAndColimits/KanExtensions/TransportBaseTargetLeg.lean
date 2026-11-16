module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLegHom

/-!
概要：既存の輸送の選択空間からの終点評価は、元のcosliceの脚を保つ。
方針：同じ評価の射影を合成し、既存の余錐の脚の自然性を使う。
規約：HTT §2.4.1、Kerodon §5.1（Tag 01T1）の既存輸送の計算法則。
使われ方：S8 の右Kanの指定輸送の比較で、頂点の射だけに情報を落とさない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 選択空間内の任意の射を終点で評価すると、元の輸送の脚の合成式を得る。 -/
lemma transportBaseFiberTarget_leg_comp_projection {E B : SSet.{u}} [Quasicategory E]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (b : B _⦋0⦌)
    (v w : (transportBaseFiber a p b) _⦋0⦌)
    (m : (HomotopyCategory.mk v : hoFunctor.obj
      (transportBaseFiber a p b)) ⟶ HomotopyCategory.mk w) :
    let J := vertexFiberι (cocartesianCosliceProjection a p ≫ sliceUnderProjection (a ≫ p)) b ≫ cocartesianCosliceι a p
    Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ v) (𝟙 Δ[0])) ≫
      (hoFunctor.map (vertexFiberι p b)).toFunctor.map
        ((hoFunctor.map (transportBaseFiberTarget a p b)).toFunctor.map m) =
          Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ w) (𝟙 Δ[0])) := by
  let J := vertexFiberι (cocartesianCosliceProjection a p ≫ sliceUnderProjection (a ≫ p)) b ≫ cocartesianCosliceι a p
  have h := JoinCocone.leg_comp_projection_hom (J.app _ v) (J.app _ w)
    ((hoFunctor.map J).toFunctor.map m) (𝟙 Δ[0])
  have hp : (hoFunctor.map (transportBaseFiberTarget a p b)).toFunctor ⋙
      (hoFunctor.map (vertexFiberι p b)).toFunctor =
        (hoFunctor.map J).toFunctor ⋙ (hoFunctor.map (sliceUnderProjection a)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Cat.Hom.comp_toFunctor,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hm : (hoFunctor.map (vertexFiberι p b)).toFunctor.map
      ((hoFunctor.map (transportBaseFiberTarget a p b)).toFunctor.map m) =
      (hoFunctor.map (sliceUnderProjection a)).toFunctor.map
        ((hoFunctor.map J).toFunctor.map m) := by
    have hh := (eqToHom hp).naturality m
    simpa only [eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id,
      Functor.comp_map] using hh
  rw [hm]
  exact h


/-- 基底写像空間の同型から得た既存の終点比較は、元の脚との合成式を保つ。 -/
lemma transportBaseFiberTargetIso_leg_comp_projection {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) (v w : (transportBaseFiber a p b) _⦋0⦌)
    (e : VertexIso ((transportBaseFiberMap a p b).app _ v)
      ((transportBaseFiberMap a p b).app _ w)) :
    let J := vertexFiberι (cocartesianCosliceProjection a p ≫
      sliceUnderProjection (a ≫ p)) b ≫ cocartesianCosliceι a p
    Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ v) (𝟙 Δ[0])) ≫
      (hoFunctor.map (vertexFiberι p b)).toFunctor.map
        (transportBaseFiberTargetIso a p b v w e).hom =
          Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ w) (𝟙 Δ[0])) := by
  let q := transportBaseFiberMap a p b
  let hq := (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration q).isFullyFaithful.toHoFullyFaithful
  simpa only [transportBaseFiberTargetIso, VertexIso.map, Functor.mapIso_hom] using
    transportBaseFiberTarget_leg_comp_projection a p b v w (hq.preimageIso (X := HomotopyCategory.mk v) (Y := HomotopyCategory.mk w) e).hom

/-- 基底の同じ辺の類から得る既存の終点比較を、元の脚との両立を付けて取り出す。 -/
lemma transportBaseFiberTarget_nonempty_iso_with_leg_of_homMk_eq {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) (v w : (transportBaseFiber a p b) _⦋0⦌)
    (h : Truncated.HomotopyCategory.homMk
      (cosliceFiberEdge (a ≫ p) b ((transportBaseFiberMap a p b).app _ v)) =
        Truncated.HomotopyCategory.homMk
          (cosliceFiberEdge (a ≫ p) b ((transportBaseFiberMap a p b).app _ w))) :
    let J := vertexFiberι (cocartesianCosliceProjection a p ≫
      sliceUnderProjection (a ≫ p)) b ≫ cocartesianCosliceι a p
    ∃ e : VertexIso ((transportBaseFiberTarget a p b).app _ v)
        ((transportBaseFiberTarget a p b).app _ w),
      Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ v) (𝟙 Δ[0])) ≫
        (hoFunctor.map (vertexFiberι p b)).toFunctor.map e.hom =
          Truncated.HomotopyCategory.homMk (JoinCocone.leg (J.app _ w) (𝟙 Δ[0])) := by
  obtain ⟨e⟩ := cosliceFiber_nonempty_iso_of_homMk_eq (a ≫ p) b _ _ h
  exact ⟨transportBaseFiberTargetIso a p b v w e,
    transportBaseFiberTargetIso_leg_comp_projection a p b v w e⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
