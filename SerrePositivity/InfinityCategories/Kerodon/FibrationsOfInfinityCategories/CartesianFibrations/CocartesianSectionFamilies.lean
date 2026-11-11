module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation

/-!
概要：任意のパラメータを持つ cocartesian section の族を実際の直積上の図式と対応させる。
方針：相対関手空間の curry と uncurry を全部分複体の頂点条件へ制限する。
規約：パラメータごとに section の方向の全辺を cocartesian に送る。
使われ方：始対象での評価の相対境界持ち上げの構成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.InfinityCategories

/-- 概要：関手の族をパラメータの一頂点に制限すると、その頂点の関手を得る。
方針：単位からの射の閉構造の同値と uncurry の自然性を使う。
規約：単体集合の充填性は不要。
使われ方：cocartesian section の族の頂点の辺の計算。 -/
lemma functorVertex_parameter {A T E : SSet.{u}} (g : T ⟶ (ihom A).obj E) (x : T _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (𝟙 A) (SSet.const x) ≫ uncurry g) = g.app (Opposite.op ⦋0⦌) x := by
  have h : lift (𝟙 A) (SSet.const x) ≫ uncurry g =
      uncurry' ((SSet.unitHomEquiv T).symm x ≫ g) := by
    rw [uncurry', uncurry_natural_left]
    rfl
  rw [h]
  change SSet.unitHomEquiv _ (curry' (uncurry' ((SSet.unitHomEquiv T).symm x ≫ g))) = _
  rw [curry'_uncurry']
  change g.app _ ((SSet.unitHomEquiv T) ((SSet.unitHomEquiv T).symm x)) = _
  rw [Equiv.apply_symm_apply]

/-- 概要：curry した図式のパラメータ頂点から回収する関手はその頂点への制限。
方針：関手頂点の単射性とパラメータ評価の式を使う。
規約：底の図式は a に固定する。
使われ方：全部分複体への族の持ち上げ。 -/
lemma relativeFunctorOfVertex_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (F : A ⊗ T ⟶ E) (hF : F ≫ p = fst A T ≫ a) (x : T _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorOfVertex p a
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x) =
        lift (𝟙 A) (SSet.const x) ≫ F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  have h := functorVertex_parameter (curry F) x
  rw [uncurry_curry] at h
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).apply_symm_apply
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF).app (Opposite.op ⦋0⦌) x).val).trans h.symm

/-- 概要：底上の図式の族が各パラメータ頂点で cocartesian なとき section の族へ curry する。
方針：curry した相対関手を頂点条件で全部分複体へ持ち上げる。
規約：直積の左因子が section の定義域。
使われ方：境界問題の充填から section の族へ戻す。 -/
def cocartesianSectionsCurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (F : A ⊗ T ⟶ E) (hF : F ≫ p = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (F.app (Opposite.op ⦋1⦌) (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsCocartesianSection p a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry F hF) (by
    intro x e
    rw [relativeFunctorOfVertex_curry]
    exact hc x e)

/-- 概要：section の族を底上の実際の直積図式へ展開する。
方針：全部分複体の包含後に相対 uncurry を適用する。
規約：パラメータは直積の右因子。
使われ方：境界や評価の条件を実際の射の等式へ移す。 -/
def cocartesianSectionsUncurry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) : A ⊗ T ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a)

/-- 概要：section の族を展開すると指定された底の図式に重なる。
方針：相対 uncurry の射影の式。
規約：底のパラメータ依存はない。
使われ方：cocartesian なホモトピー延長の基底の指定。 -/
lemma cocartesianSectionsUncurry_projection {A T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) :
    cocartesianSectionsUncurry g ≫ p = fst A T ≫ a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

/-- 概要：構成した section の族を展開すると元の図式になる。
方針：全部分複体の包含と相対 curry の往復。
規約：辺の条件の証明の選択には依存しない。
使われ方：境界や評価との厳密な一致を回収する。 -/
lemma cocartesianSectionsUncurry_curry {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (F : A ⊗ T ⟶ E) (hF : F ≫ p = fst A T ≫ a)
    (hc : ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      (F.app (Opposite.op ⦋1⦌) (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) :
    cocartesianSectionsUncurry (cocartesianSectionsCurry F hF hc) = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry F hF

/-- 概要：section の族は実際の図式への展開から一意に決まる。
方針：元の相対関手空間の単射性と全部分複体の包含の単射性を使う。
規約：任意のパラメータに対する射の単射性。
使われ方：境界の族の等式の検証。 -/
lemma cocartesianSectionsUncurry_injective {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    Function.Injective (cocartesianSectionsUncurry (T := T) (p := p) (a := a)) := by
  intro f g h
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a)).1
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective p a h

/-- 概要：section の族の展開はパラメータの制限と可換。
方針：内部 Hom の uncurry の自然性。
規約：制限の射は任意。
使われ方：境界の充填の族としての一致。 -/
lemma cocartesianSectionsUncurry_precomp {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (g : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) (i : T ⟶ U) :
    cocartesianSectionsUncurry (i ≫ g) = (A ◁ i) ≫ cocartesianSectionsUncurry g := by
  simpa only [cocartesianSectionsUncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry, Category.assoc] using
    uncurry_natural_left i (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))

/-- 概要：section の族の一頂点から回収した関手は、その頂点への実際の制限。
方針：内部 Hom の関手頂点の単射性とパラメータ評価を使う。
規約：充填性を仮定しない。
使われ方：族の各頂点の cocartesian 条件を展開する。 -/
lemma cocartesianSectionsUncurry_vertex {A T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) (x : T _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorOfVertex p a
      ((g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a).app (Opposite.op ⦋0⦌) x) =
        lift (𝟙 A) (SSet.const x) ≫ cocartesianSectionsUncurry g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).apply_symm_apply _).trans
    (functorVertex_parameter
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) x).symm

/-- 概要：展開した族は section 方向の全ての辺を cocartesian に送る。
方針：各パラメータ頂点の全部分複体の条件を回収する。
規約：パラメータの辺には条件を課さない。
使われ方：指定した部分上の cocartesian な輸送の検証。 -/
lemma cocartesianSectionsUncurry_cocartesian {A T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a)
    (x : T _⦋0⦌) (e : A _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
      ((cocartesianSectionsUncurry g).app (Opposite.op ⦋1⦌)
        (e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections_vertex p a (g.app (Opposite.op ⦋0⦌) x) e
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorOfVertex p a
      ((g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a).app (Opposite.op ⦋0⦌) x)).app _ e) at h
  rw [cocartesianSectionsUncurry_vertex] at h
  exact h

/-- 概要：cocartesian section を指定頂点で評価して、その底の fiber へ送る。
方針：全部分複体の包含と相対関手の評価を合成する。
規約：始対象性や充填性は定義には不要。
使われ方：始対象における fiber 比較。 -/
def cocartesianSectionsEvaluate {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (v : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a v

/-- 概要：族を指定した頂点で制限すると、評価射の後の fiber 包含になる。
方針：内部 Hom の評価と uncurry を各単体で計算する。
規約：評価の一致は全パラメータ上の射の等式。
使われ方：構成した延長の評価条件を section の族へ移す。 -/
lemma cocartesianSectionsUncurry_evaluate {A T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) (v : A _⦋0⦌) :
    lift (SSet.const v) (𝟙 T) ≫ cocartesianSectionsUncurry g =
      g ≫ cocartesianSectionsEvaluate p a v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (a.app (Opposite.op ⦋0⦌) v) := by
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
