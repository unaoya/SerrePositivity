module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SliceEndpointConeComparison

/-!
概要：native な極限錐を coslice の切断の制限によって検出する。
方針：錐の図式の固定条件を正規化し、slice と切断の実際の制限の同値判定を移す。
規約：任意の単体集合上の coherent な錐を扱う。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の豊穣比較への入力。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：native な錐の slice の制限を展開すると右図式への包含による前合成になる。
方針：Yoneda 表示の正規化を除き、一般の展開した図式の制限の式を使う。
規約：任意パラメータ A の族について成立する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の実際の native な制限と通常の制限の同定。 -/
lemma coneSliceOverRestriction_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceOverRestriction c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceOverRestriction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.uncurriedSliceOverRestriction_uncurry]
  congr 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (s ≫ eqToHom
    (congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda 0 c).symm)) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverUncurry_eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda 0 c).symm s

/-- 概要：native な錐の slice の制限は、通常の図式の制限を固定条件で移送したもの。
方針：全パラメータの uncurry の単射性と移送で値が変わらないことを使う。
規約：固定条件 c.property の証明への依存はない。
使われ方：HTT 4.2.4.1 の native な制限の二対三則への入力。 -/
lemma coneSliceOverRestriction_eq {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceOverRestriction c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) ≫
        eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) c.property) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective p
  have h := coneSliceOverRestriction_uncurry c (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val))
  simp only [Category.id_comp] at h
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverUncurry_eqToHom c.property]
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver c.val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)
  simp only [Category.id_comp] at hr
  rw [hr]

/-- 概要：錐の図式上の coslice の切断を元の図式上の切断へ制限する。
方針：右図式への包含で前合成し、錐の固定条件で終域を移送する。
規約：終域は元の p の切断空間そのもの。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の native な極限判定の実際の切断の制限射。 -/
def coneSectionRestriction {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) ≫
      eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace f x) c.property)

/-- 概要：固定図式の等式で切断空間を移送しても展開した図式は変わらない。
方針：図式の等式で置換して恒等射への後合成を除く。
規約：頂点 x と図式の始域 K は共通。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の固定条件を正規化した切断の制限の値。 -/
lemma sectionConeUncurry_eqToHom {A K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (x : X _⦋0⦌) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry (s ≫
      eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace f x) h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry s := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

/-- 概要：native な切断の制限を展開すると右図式の包含による前合成になる。
方針：図式の等式による移送を除き、相対前合成の展開の自然性を使う。
規約：任意の単体的パラメータ A の全次数の値を保つ。
使われ方：HTT 4.2.4.1 の豊穣比較と native な切断の制限の可換式への入力。 -/
lemma coneSectionRestriction_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry (s ≫ coneSectionRestriction c x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ▷ A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry s := by
  rw [coneSectionRestriction, ← Category.assoc,
    sectionConeUncurry_eqToHom c.property x, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry_restrict]

/-- 概要：図式の等式で終域を正規化した slice と切断の制限の同値性は同値。
方針：図式の等式で置換し、通常の制限の同値判定に戻す。
規約：X は quasicategory。正規化の等式 h に追加の性質は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の錐の固定条件を保つ制限判定の移送。 -/
lemma normalizedSliceRestriction_iff_sections {K J X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q)
    (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f ≫ eqToHom (congrArg (fun r : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver r) h))
        (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOver_eqToHom_projection h, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverRestrict_projection])
        x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
          eqToHom (congrArg (fun r : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace r x) h)) := by
  subst q
  simpa only [eqToHom_refl, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceRestrictionFiberMap] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceRestriction_homotopyEquivalence_iff_sections p x f

/-- 概要：native な slice の制限の同値性と coslice の切断の制限の同値性は同値。
方針：slice の制限を通常の図式の制限へ同定し、正規化した同値判定を適用する。
規約：任意の coherent な錐 c と頂点 x を扱う。
使われ方：HTT 4.2.4.1 の native な極限判定の切断への移送。 -/
lemma coneSliceRestriction_homotopyEquivalence_iff_sections {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceRestrictionFiberMap c x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSectionRestriction c x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSliceRestrictionFiberMap
  have h := normalizedSliceRestriction_iff_sections c.val p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) c.property x
  simpa only [← coneSliceOverRestriction_eq, coneSectionRestriction] using h

/-- 概要：coherent な錐の極限性は全頂点での coslice の切断の制限の同値性で検出できる。
方針：A3d に基づく native な slice の判定を実際の切断の制限へ移す。
規約：K は任意の単体集合、X の quasicategory 性のみを仮定する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の豊穣比較の入力となる極限判定。 -/
lemma isLimitCone_iff_coneSectionRestriction_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coneSectionRestriction c x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_coneSliceRestrictionFiberMap_homotopyEquivalence]
  exact forall_congr' (fun x ↦ coneSliceRestriction_homotopyEquivalence_iff_sections c x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
