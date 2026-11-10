module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramExtensionSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFiber
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportEvaluation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：scaffold の豊穣写像空間同型から、通常の自然変換と底上の射の随伴対応を取り出す。
方針：両写像空間の頂点表示の全単射を同型の零単体で結ぶ。
規約：図式や射影の充填性を要求しない厳密な対応。
使われ方：Kerodon §§5.3.1–5.3.4、strict 図式と復元した fibration の比較の単位の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：通常の自然変換と strict な変換空間の頂点は全単射。
方針：構成済みの頂点表示の単射性と全射性を束ねる。
規約：対象ごとでなく図式全体の自然変換を対応させる。
使われ方：Kerodon §5.3.1、scaffold の写像空間同型を通常の射の対応にする。 -/
noncomputable def strictDiagramMappingVertexEquiv {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) : (F ⟶ G) ≃ (strictDiagramMappingSpace F G) _⦋0⦌ :=
  Equiv.ofBijective strictDiagramMappingVertex
    ⟨strictDiagramMappingVertex_injective F G, exists_strictDiagramMappingVertex F G⟩

/-- 概要：strict transport への自然変換と replacement 上の底を保つ射は全単射。
方針：頂点表示、scaffold の写像空間同型の零単体、相対関手の頂点表示を順に合成する。
規約：順方向は既存の scaffold 評価そのもの。
使われ方：Kerodon §§5.3.1–5.3.4、復元比較から図式の比較を構成する。 -/
@[kerodon 036G]
noncomputable def strictDiagramScaffoldHomEquiv {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    (F ⟶ leftStrictTransportDiagram q) ≃
      {f : simplicialReplacement F ⟶ E // f ≫ q = simplicialReplacementProjection F} :=
  ((strictDiagramMappingVertexEquiv F (leftStrictTransportDiagram q)).trans
    ((strictDiagramMappingScaffoldIso F q).app (Opposite.op ⦋0⦌)).toEquiv).trans
      (relativeFunctorVertexEquiv q (simplicialReplacementProjection F)).symm

/-- 概要：scaffold の通常の随伴対応の順方向は、自然変換の頂点の scaffold 評価。
方針：相対関手の頂点表示の往復を消す。
規約：得られた底上の射そのものを比較する。
使われ方：Kerodon §5.3.4、随伴対応で構成した単位の頂点での計算。 -/
lemma strictDiagramScaffoldHomEquiv_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (θ : F ⟶ leftStrictTransportDiagram q) :
    relativeFunctorVertex q (simplicialReplacementProjection F)
      (strictDiagramScaffoldHomEquiv F q θ).val
      (strictDiagramScaffoldHomEquiv F q θ).property =
    (strictDiagramMappingScaffoldMap F q).app (Opposite.op ⦋0⦌)
      (strictDiagramMappingVertex θ) :=
  (relativeFunctorVertexEquiv q (simplicialReplacementProjection F)).apply_symm_apply _

/-- 概要：scaffold の通常の随伴対応の逆方向は相対関手の頂点への scaffold 逆射。
方針：strict な変換の頂点表示の往復を消す。
規約：逆向きでも一つの自然変換として比較する。
使われ方：Kerodon §§5.3.1–5.3.4、底上の復元比較を図式全体の比較へ戻す。 -/
lemma strictDiagramScaffoldHomEquiv_symm_vertex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : simplicialReplacement F ⟶ E // f ≫ q = simplicialReplacementProjection F}) :
    strictDiagramMappingVertex ((strictDiagramScaffoldHomEquiv F q).symm h) =
      (strictDiagramMappingScaffoldInverse F q).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex q (simplicialReplacementProjection F) h.val h.property) :=
  (strictDiagramMappingVertexEquiv F (leftStrictTransportDiagram q)).apply_symm_apply _

/-- 概要：底上の射を自然変換へ戻す対応は undercategory の普遍評価で全単体を計算できる。
方針：逆対応の頂点の式を各成分とパラメーターで評価し、scaffold 逆射の式を使う。
規約：n と m および単体圏の反対圏の射 α は任意。
使われ方：Kerodon §5.3.4、構成した図式の比較の評価と高次の自然性の計算。 -/
lemma strictDiagramScaffoldHomEquiv_symm_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : simplicialReplacement F ⟶ E // f ≫ q = simplicialReplacementProjection F})
    (c : C) (n m : SimplexCategoryᵒᵖ) (x : (F.obj c).obj n) (α : n ⟶ m)
    (τ : (nerve (Under c)).obj m) :
    ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app n x).val.app m α τ =
      h.val.app m ((simplicialReplacementUnderEvaluation F c).app m (τ, (F.obj c).map α x)) := by
  let β : Opposite.op ⦋0⦌ ⟶ n := (SimplexCategory.const n.unop ⦋0⦌ 0).op
  have hh := congrArg
    (fun η : (strictDiagramMappingSpace F (leftStrictTransportDiagram q)) _⦋0⦌ ↦
      ((η.val c).app n β x).val.app m α τ)
    (strictDiagramScaffoldHomEquiv_symm_vertex F q h)
  change ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app n x).val.app m α τ =
    ((((strictDiagramScaffoldInverseComponent F q c).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex q (simplicialReplacementProjection F) h.val h.property)).app n β x).val.app
        m α τ) at hh
  rw [strictDiagramScaffoldInverseComponent_app] at hh
  exact hh

/-- 概要：scaffold の逆対応で作った比較を恒等射で評価すると、元の射の定値係数での値になる。
方針：under の恒等射の定値単体を成分の評価式へ代入し、係数図式の恒等則を使う。
規約：fiber の包含後の射の厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6、図式の単位の同値性を元の fiber 比較で検出する。 -/
lemma strictDiagramScaffoldHomEquiv_symm_evaluate_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C)
    (h : {f : simplicialReplacement F ⟶ E // f ≫ q = simplicialReplacementProjection F}) (c : C) :
    ((strictDiagramScaffoldHomEquiv F q).symm h).app c ≫ leftStrictTransportEvaluate q c ≫
      vertexFiberι q (nerveVertex c) = simplicialReplacementConstantLift F c ≫ h.val := by
  erw [leftStrictTransportEvaluate_ι q c]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change ((((strictDiagramScaffoldHomEquiv F q).symm h).app c).app (Opposite.op ⦋n⦌) x).val.app
    (Opposite.op ⦋n⦌) (𝟙 _) (PinchedHom.constant (strictTransportUnderIdentityVertex c) n) = _
  rw [strictDiagramScaffoldHomEquiv_symm_app, Functor.map_id_apply]
  apply congrArg (fun z : (simplicialReplacement F) _⦋n⦌ ↦ h.val.app (Opposite.op ⦋n⦌) z)
  change (⟨(Functor.const (Fin (n + 1))).obj c,
    SSet.yonedaEquiv.symm x ≫ F.map (𝟙 c)⟩ : simplicialReplacementSimplex F n) =
      ⟨(Functor.const (Fin (n + 1))).obj c, SSet.yonedaEquiv.symm x⟩
  rw [F.map_id, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories
