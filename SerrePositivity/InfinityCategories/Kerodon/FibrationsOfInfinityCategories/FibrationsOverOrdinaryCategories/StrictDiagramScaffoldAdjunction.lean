module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportEvaluation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：scaffold の豊穣写像空間同型から、通常の自然変換と底上の射の随伴対応を取り出す。
方針：両写像空間の頂点表示の全単射を同型の零単体で結ぶ。
規約：図式や射影の充填性を要求しない厳密な対応。
使われ方：Kerodon §§5.3.1（Tag 035D）–5.3.4（Tag 036V）、strict 図式と復元した fibration の比較の単位の構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：通常の自然変換と strict な変換空間の頂点は全単射。
方針：構成済みの頂点表示の単射性と全射性を束ねる。
規約：対象ごとでなく図式全体の自然変換を対応させる。
使われ方：Kerodon §5.3.1（Tag 035D）、scaffold の写像空間同型を通常の射の対応にする。 -/
noncomputable def strictDiagramMappingVertexEquiv {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) : (F ⟶ G) ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) _⦋0⦌ :=
  Equiv.ofBijective _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex_injective F G, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_strictDiagramMappingVertex F G⟩

/-- 概要：strict transport への自然変換と replacement 上の底を保つ射は全単射。
方針：頂点表示、scaffold の写像空間同型の零単体、相対関手の頂点表示を順に合成する。
規約：順方向は既存の scaffold 評価そのもの。
使われ方：Kerodon §§5.3.1（Tag 035D）–5.3.4（Tag 036V）、復元比較から図式の比較を構成する。 -/
@[kerodon 036G]
noncomputable def strictDiagramScaffoldHomEquiv {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    (F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≃
      {f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E // f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F} :=
  ((strictDiagramMappingVertexEquiv F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldIso F q).app (Opposite.op ⦋0⦌)).toEquiv).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).symm

/-- 概要：scaffold の通常の随伴対応の順方向は、自然変換の頂点の scaffold 評価。
方針：相対関手の頂点表示の往復を消す。
規約：得られた底上の射そのものを比較する。
使われ方：Kerodon §5.3.4（Tag 036V）、随伴対応で構成した単位の頂点での計算。 -/
lemma strictDiagramScaffoldHomEquiv_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)
      (strictDiagramScaffoldHomEquiv F q θ).val
      (strictDiagramScaffoldHomEquiv F q θ).property =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex θ) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).apply_symm_apply _

/-- 概要：scaffold の通常の随伴対応の逆方向は相対関手の頂点への scaffold 逆射。
方針：strict な変換の頂点表示の往復を消す。
規約：逆向きでも一つの自然変換として比較する。
使われ方：Kerodon §§5.3.1（Tag 035D）–5.3.4（Tag 036V）、底上の復元比較を図式全体の比較へ戻す。 -/
lemma strictDiagramScaffoldHomEquiv_symm_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E // f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingVertex ((strictDiagramScaffoldHomEquiv F q).symm h) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingScaffoldInverse F q).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) h.val h.property) :=
  (strictDiagramMappingVertexEquiv F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)).apply_symm_apply _

/-- 概要：底上の射を自然変換へ戻す対応は undercategory の普遍評価で全単体を計算できる。
方針：逆対応の頂点の式を各成分とパラメーターで評価し、scaffold 逆射の式を使う。
規約：n と m および単体圏の反対圏の射 α は任意。
使われ方：Kerodon §5.3.4（Tag 036V）、構成した図式の比較の評価と高次の自然性の計算。 -/
lemma strictDiagramScaffoldHomEquiv_symm_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E // f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F})
    (c : C) (n m : SimplexCategoryᵒᵖ) (x : (F.obj c).obj n) (α : n ⟶ m)
    (τ : (nerve (Under c)).obj m) :
    ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app n x).val.app m α τ =
      h.val.app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app m (τ, (F.obj c).map α x)) := by
  let β : Opposite.op ⦋0⦌ ⟶ n := (SimplexCategory.const n.unop ⦋0⦌ 0).op
  have hh := congrArg
    (fun η : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)) _⦋0⦌ ↦
      ((η.val c).app n β x).val.app m α τ)
    (strictDiagramScaffoldHomEquiv_symm_vertex F q h)
  change ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app n x).val.app m α τ =
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent F q c).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) h.val h.property)).app n β x).val.app
        m α τ) at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramScaffoldInverseComponent_app] at hh
  exact hh

/-- 概要：scaffold の逆対応で作った比較を恒等射で評価すると、元の射の定値係数での値になる。
方針：under の恒等射の定値単体を成分の評価式へ代入し、係数図式の恒等則を使う。
規約：fiber の包含後の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、図式の単位の同値性を元の fiber 比較で検出する。 -/
lemma strictDiagramScaffoldHomEquiv_symm_evaluate_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E // f ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F}) (c : C) :
    ((strictDiagramScaffoldHomEquiv F q).symm h).app c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportEvaluate q c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F c ≫ h.val := by
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportEvaluate_ι q c]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app (Opposite.op ⦋n⦌) x).val.app
    (Opposite.op ⦋n⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportUnderIdentityVertex c) n) = _
  rw [strictDiagramScaffoldHomEquiv_symm_app, Functor.map_id_apply]
  apply congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) _⦋n⦌ ↦ h.val.app (Opposite.op ⦋n⦌) z)
  change (⟨(Functor.const (Fin (n + 1))).obj c,
    SSet.yonedaEquiv.symm x ≫ F.map (𝟙 c)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F n) =
      ⟨(Functor.const (Fin (n + 1))).obj c, SSet.yonedaEquiv.symm x⟩
  rw [F.map_id, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
