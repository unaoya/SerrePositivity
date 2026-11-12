module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftTransport

/-!
概要：係数の射を weighted nerve の二つの係数包含の間の prism として構成する。
方針：under-category の恒等射から指定された射への辺を、始点の係数値とともに評価する。
規約：係数の Kan 性は prism の構成と端点の計算には不要。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 値図式の射が fiber 間の transport を表すことの証人。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：辺を第一因子に写す直積の射は prism の始点を辺の始点に写す。
方針：直積への包含の計算と辺の始点での Yoneda 評価を使う。
規約：パラメーター A は任意。
使われ方：Kerodon §5.3.3（Tag 025W）、under-category の辺の prism の初期値。 -/
lemma prismEndpoint_edge_source {X A : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ (SSet.yonedaEquiv.symm e.edge ▷ A) =
      lift (SSet.const a) (𝟙 A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_whiskerRight]
  congr 1
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_zero (A := A) e.edge
  change (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : A ⟶ Δ[1]) ≫
    SSet.yonedaEquiv.symm e.edge = SSet.const (X.δ 1 e.edge) at h
  exact h.trans (congrArg (fun x ↦ (SSet.const x : A ⟶ X)) e.src_eq)

/-- 概要：辺を第一因子に写す直積の射は prism の終点を辺の終点に写す。
方針：直積への包含の計算と辺の終点での Yoneda 評価を使う。
規約：パラメーター A は任意。
使われ方：Kerodon §5.3.3（Tag 025W）、under-category の辺の prism の終端値。 -/
lemma prismEndpoint_edge_target {X A : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (SSet.yonedaEquiv.symm e.edge ▷ A) =
      lift (SSet.const b) (𝟙 A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_whiskerRight]
  congr 1
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one (A := A) e.edge
  change (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : A ⟶ Δ[1]) ≫
    SSet.yonedaEquiv.symm e.edge = SSet.const (X.δ 0 e.edge) at h
  exact h.trans (congrArg (fun x ↦ (SSet.const x : A ⟶ X)) e.tgt_eq)

/-- 概要：係数の射に沿って始点の係数包含から終点の係数包含へ移る prism。
方針：under の恒等対象から f の対象への辺を under の係数評価に代入する。
規約：prism の底は元の圏の f に対応する nerve の辺。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の射を weighted nerve の transport とする持ち上げ。 -/
noncomputable def weightedNerveTransportPrism {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    (Δ[1] : SSet.{u}) ⊗ F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F :=
  (SSet.yonedaEquiv.symm (nerve.edgeMk
    (Under.homMk f : Under.mk (𝟙 c) ⟶ Under.mk f)).edge ▷ F.obj c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation F c

/-- 概要：係数輸送の prism の始点は始点の係数の標準包含。
方針：under の始点での評価と係数関手の恒等則を使う。
規約：fiber の同型をまだ合成せず全空間への包含で表す。
使われ方：Kerodon §5.3.3（Tag 025W）、transport の始点条件。 -/
lemma weightedNerveTransportPrism_zero {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ weightedNerveTransportPrism F f = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F c := by
  rw [weightedNerveTransportPrism, ← Category.assoc, prismEndpoint_edge_source]
  change lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 c)))) (𝟙 (F.obj c)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation F c = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation_at]
  change F.map (𝟙 c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F c = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- 概要：係数輸送の prism の終点は係数の射と終点の標準包含の合成。
方針：under の終点が表す射 f での評価を使う。
規約：F.map f は単体集合の射そのもの。
使われ方：Kerodon §5.3.3（Tag 025W）、transport の終点条件。 -/
lemma weightedNerveTransportPrism_one {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ weightedNerveTransportPrism F f =
      F.map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F d := by
  rw [weightedNerveTransportPrism, ← Category.assoc, prismEndpoint_edge_target]
  change lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk f))) (𝟙 (F.obj c)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation F c = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation_at]
  rfl

/-- 概要：係数輸送の prism は指定した f の nerve の辺の定値族を被覆する。
方針：under の忘却による底の式と、直積の第一射影を計算する。
規約：始点の係数のパラメーターを底では忘れる。
使われ方：Kerodon §5.3.3（Tag 025W）、transport の底上の持ち上げ条件。 -/
lemma weightedNerveTransportPrism_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    weightedNerveTransportPrism F f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      fst (Δ[1] : SSet.{u}) (F.obj c) ≫ SSet.yonedaEquiv.symm (nerve.edgeMk f).edge := by
  rw [weightedNerveTransportPrism, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveUnderEvaluation_projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc, SSet.yonedaEquiv_symm_comp]
  congr 2
  apply ComposableArrows.ext₁ (by rfl) (by rfl)
  simp
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
