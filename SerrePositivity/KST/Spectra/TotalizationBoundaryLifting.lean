module

public import SerrePositivity.KST.Spectra.TotalizationFibration
public import SerrePositivity.KST.Spectra.BoundaryTensorMonomorphism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：通常の Tot による相対 matching 全ての単射に対する RLP の保存。
方針：境界を tensor した標準単体の Reedy 単射性と Reedy 持ち上げを使う。
規約：全ての単射に対する RLP は全ての単射に対する右持ち上げ性を意味する。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot のホモトピー比較の基礎。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open HomotopicalAlgebra SSet
open SerrePositivity.Reedy
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.CosimplicialTotalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：パラメーター付き図式の持ち上げを Tot の持ち上げへ移す。
方針：curry・uncurry の往復と前合成・後合成の自然性を使う。
規約：射 i の単射性も horn 条件も仮定しない。
使われ方：Goerss–Jardine VIII §1。Tot の持ち上げ随伴の具体形。 -/
lemma map_hasLiftingProperty {A B : SSet.{u}} (i : A ⟶ B)
    {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)
    [HasLiftingProperty (SimplexTensorBoundary.map i) f] :
    HasLiftingProperty i (map f) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  let q : CommSq (uncurry a) (SimplexTensorBoundary.map i) f (uncurry b) :=
    ⟨by
      rw [← uncurry_map, ← uncurry_pre]
      exact congrArg uncurry sq.w⟩
  refine ⟨⟨{ l := lift q.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [lift_pre, q.fac_left, lift_uncurry]
  · rw [lift_post, q.fac_right, lift_uncurry]

/-- 概要：相対 matching が全ての単射に対する RLP な射は Tot 上でも全ての単射に対する RLP。
方針：境界のパラメーターの Reedy 単射性から全ての境界の充填を構成する。
規約：相対 matching の条件であり、対象ごとの充填だけで代用しない。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の acyclic な比較射。 -/
lemma map_rlp_monomorphisms {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (map f) := by
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have hi := SimplexTensorBoundary.boundaryMap_reedy_mono.{u} n
  let : ∀ j, HasLiftingProperty
      (relativeLatchingMap simplex j (SimplexTensorBoundary.map (SSet.boundary.{u} n).ι))
      (relativeMatchingMap simplex j f) :=
    fun j ↦ hf j _ (hi j)
  let : HasLiftingProperty (SimplexTensorBoundary.map (SSet.boundary.{u} n).ι) f :=
    Lifting.hasLiftingProperty simplex
  exact map_hasLiftingProperty (SSet.boundary.{u} n).ι f

/-- 概要：相対 matching が全ての単射に対する RLP な比較は Kan な Tot の全基点 π_* 同型。
方針：Tot 上の全ての単射に対する RLP から Kan ホモトピー群の同型を得る。
規約：両 Tot の Kan 性と相対 matching の右持ち上げ性を明示する。
使われ方：Goerss–Jardine VIII §1。Tot の比較の π_* への移送。 -/
lemma map_piIsomorphism_of_matching_monoRight
    {X Y : CosimplicialObject SSet.{u}} [KanComplex (obj X)] [KanComplex (obj Y)]
    (f : X ⟶ Y)
    (hf : reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (map f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (map_rlp_monomorphisms f hf)

end

end SerrePositivity.KST.Spectra.CosimplicialTotalization
