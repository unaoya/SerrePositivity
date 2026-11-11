module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection

/-!
概要：weighted nerve から left fibration への比較射を介して係数の射と transport を比較する。
方針：weighted nerve の係数輸送と、底上の射に関する transport の自然性を合成する。
規約：比較射自体の自然性の選択は要求せず、底上の射であることを使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の作用を元の Kan 値図式の射と照合する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：weighted nerve の比較射から、係数値と標的の fiber の間の射を作る。
方針：係数値の標準 fiber 同型と比較射の fiber への作用を合成する。
規約：比較射 h は通常の nerve の底を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の対象での比較。 -/
noncomputable def weightedNerveComparisonFiber {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (c : C) :
    F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F c).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) q h hh (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)

/-- 概要：weighted nerve の比較射の下で、係数の射と標的の transport は関手同型まで可換。
方針：係数での標準 transport の式を、比較射に関する transport の自然性に合成する。
規約：同型は係数値 F(c) から標的の終点 fiber への射の間で取る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な Kan 図式と coherent な復元の射への作用の比較。 -/
noncomputable def weightedNerveComparisonFiber_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
    {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (F.map f ≫ weightedNerveComparisonFiber F q h hh d)
      (weightedNerveComparisonFiber F q h hh c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (nerve.edgeMk f)) := by
  have e₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTransport_coefficientIso F f).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F d).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) q h hh (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d))
  have e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) q h hh (nerve.edgeMk f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F c).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at e₀
  have e := e₀ ≪≫ e₁
  exact e

/-- 概要：比較射が fiber で同値なら、係数から標的 fiber への比較も同値。
方針：標準 fiber 同型の同値性と与えた fiber 射の同値性を合成する。
規約：指定された一対象 c での同値性だけを仮定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元の fiber 同値を係数での比較へ移す。 -/
lemma weightedNerveComparisonFiber_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (c : C)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) q h hh (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F c)).isQCatEquivalence.comp hc

/-- 概要：比較射が両端の係数値で同値なら、標的 transport の同値性は係数の射で判定できる。
方針：係数と transport の自然性の同型と両端の同値に二対三則を適用する。
規約：比較射の全空間の同値性は仮定せず、必要な二つの fiber の比較だけを使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の射の同値性の係数による検出。 -/
lemma weightedNerveComparison_transport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
    {c d : C} (f : c ⟶ d)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (weightedNerveComparisonFiber F q h hh d)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (nerve.edgeMk f)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F.map f) := by
  have e := weightedNerveComparisonFiber_transportIso F q h hh f
  constructor
  · intro he
    exact hd.cancel_right ((hc.comp he).ofFunctorIso e.symm)
  · intro he
    exact hc.cancel_left ((he.comp hd).ofFunctorIso e)

/-- 概要：weighted nerve の比較射が全空間の前合成同値なら、係数と標的 fiber の比較は全対象で同値。
方針：相対逆による fiber の同値性の回収と標準 fiber 同型を使う。
規約：底は通常の圏の nerve なので quasicategory の条件を満たす。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元の全空間比較から値の同値を回収する。 -/
lemma weightedNerveComparisonFiber_isQCatEquivalence_of_precompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
    (eh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence h) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (weightedNerveComparisonFiber F q h hh c) :=
  weightedNerveComparisonFiber_isQCatEquivalence F q h hh c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) q h hh eh (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))

/-- 概要：weighted nerve と同値な left fibration の標準 transport の同値性は係数の射で判定できる。
方針：全空間の比較から両端の fiber 同値を回収し、係数と transport の比較を適用する。
規約：fiber ごとの同値性を別途仮定せず、実際の底上の前合成同値射 h を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較を介して coherent な作用の同値性を検出する。 -/
lemma weightedNerveComparison_transport_isQCatEquivalence_iff_of_precompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ E) (hh : h ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
    (eh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence h) {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (nerve.edgeMk f)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (F.map f) :=
  weightedNerveComparison_transport_isQCatEquivalence_iff F q h hh f
    (weightedNerveComparisonFiber_isQCatEquivalence_of_precompositionEquivalence F q h hh eh c)
    (weightedNerveComparisonFiber_isQCatEquivalence_of_precompositionEquivalence F q h hh eh d)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
