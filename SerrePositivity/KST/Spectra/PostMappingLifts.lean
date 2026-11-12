module

public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeProductLifting

/-!
概要：全ての単射への RLP は点つき Hom の標的変数で保存される。
方針：パラメータの単射と源の基点包含の pushout product を持ち上げる。
規約：源にも標的にも Kan 性を要求しない。
使われ方：BF 1978 §2、HTT A.3.3。置換の比較射を loop に移す。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全ての単射への右持ち上げ性は点つき内部 Hom の後合成で保存される。
方針：基点上の定数族と既存パラメータ族を同時に保つ相対積の持ち上げを使う。
規約：RLP の仮定だけを使い、弱同値クラスは不要。
使われ方：BF 1978 §2、HTT A.3.3。loop による置換射の π_* 保存。 -/
theorem post_rlp_monomorphisms (A : PointedSimplicialSet.{u})
    {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (PointedObject.basedHomMap A p).right := by
  intro T U j hj
  let : Mono j := hj
  let : Mono A.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono A
  constructor
  intro a b sq
  let earlier := MonoidalClosed.uncurry (a ≫ PointedObject.basedHomι A E)
  let prescribed := toUnit (𝟙_ SSet.{u} ⊗ U) ≫ E.hom
  let base := MonoidalClosed.uncurry (b ≫ PointedObject.basedHomι A B)
  have hc : A.hom ▷ T ≫ earlier = 𝟙_ SSet.{u} ◁ j ≫ prescribed := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
    simp only [prescribed, comp_toUnit_assoc]
  have he : earlier ≫ p.right = A.right ◁ j ≫ base := by
    dsimp only [earlier, base]
    rw [← MonoidalClosed.uncurry_natural_right, Category.assoc,
      ← PointedObject.basedHomMap_ι, ← Category.assoc, sq.w,
      MonoidalClosed.uncurry_natural_left]
    rfl
  have ha : prescribed ≫ p.right = A.hom ▷ U ≫ base := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
    simp only [prescribed, Category.assoc, Under.w]
  obtain ⟨f, hf, hfixed, hbase⟩ := RelativeProductLifting.exists_lift
    p.right hp A.hom j earlier prescribed base hc he ha
  let l := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E f hfixed
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (PointedObject.basedHomι A E)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_left,
      hf, MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι A B)).mp
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_right, hbase,
      MonoidalClosed.curry_uncurry]

end

end SerrePositivity.KST.Spectra.PointedMapping
