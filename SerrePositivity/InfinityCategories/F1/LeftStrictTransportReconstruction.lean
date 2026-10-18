module

public import SerrePositivity.InfinityCategories.F1.LeftScaffoldComparison
public import SerrePositivity.InfinityCategories.F1.OverComparisonResolution

/-!
概要：left fibration の strict transport の weighted nerve と元の全空間の比較。
方針：taut・universal scaffold の共通の始域を置換し、底上の前合成同値の span を得る。
規約：共通の始域の射影には inner fibration 性を記録し、left fibration 性は主張しない。
使われ方：Kerodon Theorem 5.3.5.6、strict transport による全空間の復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：strict transport の weighted nerve と元の全空間は底上の前合成同値の span で結ばれる。
方針：二つの scaffold に共通の inner anodyne 置換からの比較を延長する。
規約：共通の始域は通常の nerve 上の inner fibration の全空間なので quasicategory。
使われ方：Kerodon Theorem 5.3.5.6、通常の底上での strict transport の復元比較。 -/
lemma exists_leftStrictTransport_reconstruction_span
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    ∃ (Z : SSet.{u}) (t : Z ⟶ nerve C) (a : Z ⟶ E)
      (b : Z ⟶ leftStrictTransportWeightedNerve p),
      InnerFibration t ∧ a ≫ p = t ∧ b ≫ leftStrictTransportWeightedProjection p = t ∧
      IsPrecompositionEquivalence a ∧ IsPrecompositionEquivalence b := by
  obtain ⟨Z, i, t, a, b, _, ht, _, _, _, ha, hb, ea, eb⟩ :=
    exists_innerFibration_comparison_span
      (simplicialReplacementProjection (leftStrictTransportDiagram p)) p
      (leftStrictTransportWeightedProjection p) (universalScaffold p)
      (tautScaffold (leftStrictTransportDiagram p))
      (universalScaffold_projection p) (tautScaffold_projection (leftStrictTransportDiagram p))
      (universalScaffold_isPrecompositionEquivalence p)
      (tautScaffold_isPrecompositionEquivalence (leftStrictTransportDiagram p))
  exact ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩

/-- 概要：strict transport の weighted nerve と元の全空間の間に quasicategory の同値が存在する。
方針：底上の span の二つの射を quasicategory の同値とし、一方を逆にして合成する。
規約：結論の同値は全空間の同値であり、底上の厳密な比較は span の定理に保持する。
使われ方：Kerodon Theorem 5.3.5.6、strict diagram による復元の全空間での結論。 -/
lemma nonempty_leftStrictTransportTotalEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    Nonempty (QCatEquivalence E (leftStrictTransportWeightedNerve p)) := by
  obtain ⟨Z, t, a, b, ht, _, _, ea, eb⟩ := exists_leftStrictTransport_reconstruction_span p
  have : InnerFibration t := ht
  have : Quasicategory Z := quasicategory_of_innerFibration t
  exact ⟨ea.isQCatEquivalence.choose.symm.trans eb.isQCatEquivalence.choose⟩

/-- 概要：strict transport の weighted nerve への全空間の同値を選択する。
方針：底上の共通の比較から得た同値の非空性を用いる。
規約：元の全空間の quasicategory 性は p の left fibration 性からも得られる。
使われ方：Kerodon Theorem 5.3.5.6、strict transport の全空間復元を使う側の API。 -/
noncomputable def leftStrictTransportTotalEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [LeftFibration p] :
    QCatEquivalence E (leftStrictTransportWeightedNerve p) :=
  (nonempty_leftStrictTransportTotalEquivalence p).some

end SerrePositivity.InfinityCategories
