module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterDiagram
public import SerrePositivity.KST.Spectra.D3EndpointParameterSquare
public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderReindex

/-!
概要：二つの実パラメータ図式をテンソルし、全 Kan Hom と同時評価する。
方針：両順序を保持した積順序上で元の制限射をテンソルし、既証の混合 Hom 則へ代入する。
規約：二つの内部 Hom の交換同型や円交換因子の比較は使わない。
使われ方：転置模型の単位整合を調べるため、二つの端点四角形全体を一つの族に保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
variable {J : Type v} {K : Type w} [Preorder J] [Preorder K]
  (D : Jᵒᵖ ⥤ PointedSimplicialSet.{u}) (E : Kᵒᵖ ⥤ PointedSimplicialSet.{u})
local instance d3TensorParameterProductCategory : SmallCategory (J × K) :=
  Preorder.smallCategory (J × K)

/-- 元の全 Hom 共同評価は、パラメータの任意の単調な制限を厳密に保持する。 -/
lemma d3PointedKanParameterDiagram_reindex (r : J →o K) :
    (EnrichedOrderedCylinder.reindex (C := PointedKanObject.{u}) r).comp SSet
      (d3PointedKanParameterDiagram E) =
    d3PointedKanParameterDiagram (r.toFunctor.op ⋙ E) := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨p, f⟩
  change (D3EnrichedOrderedDiagram.map (d3ParameterStage E) (d3ParameterMixed E)
      ⟨r X.position, X.val⟩ ⟨r Y.position, Y.val⟩).app d
        (⟨⟨r.monotone p.down.down⟩⟩, f) =
    (D3EnrichedOrderedDiagram.map (d3ParameterStage (r.toFunctor.op ⋙ E))
      (d3ParameterMixed (r.toFunctor.op ⋙ E)) X Y).app d (p, f)
  rw [D3EnrichedOrderedDiagram.map_app, D3EnrichedOrderedDiagram.map_app]
  rfl

/-- 元の二つの逆向きパラメータ図式を、同じ積順序上で同時に保持する。 -/
def d3TensorParameter : (J × K)ᵒᵖ ⥤ PointedSimplicialSet.{u} where
  obj p := D.obj (Opposite.op p.unop.1) ⊗ E.obj (Opposite.op p.unop.2)
  map f := d3ParameterArrow D (leOfHom f.unop).1 ⊗ₘ
    d3ParameterArrow E (leOfHom f.unop).2
  map_id p := by
    rw [d3ParameterArrow_id, d3ParameterArrow_id, id_tensorHom_id]
  map_comp {p q r} f g := by
    change d3ParameterArrow D (le_trans (leOfHom g.unop).1 (leOfHom f.unop).1) ⊗ₘ
        d3ParameterArrow E (le_trans (leOfHom g.unop).2 (leOfHom f.unop).2) = _
    rw [d3ParameterArrow_comp D (leOfHom g.unop).1 (leOfHom f.unop).1,
      d3ParameterArrow_comp E (leOfHom g.unop).2 (leOfHom f.unop).2,
      tensorHom_comp_tensorHom]

/-- 同じ二つの実射は、混合 Hom で使われるパラメータ射そのもの。 -/
lemma d3TensorParameter_arrow {p q : J × K} (h : p ≤ q) :
    d3ParameterArrow (d3TensorParameter D E) h =
      d3ParameterArrow D h.1 ⊗ₘ d3ParameterArrow E h.2 := rfl

/-- 二つの全パラメータと元の Kan 入力 Hom を同時に保持する実豊穣関手。 -/
def d3TensorParameterDiagram :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (J × K) PointedKanObject.{u})
      PointedKanObject.{u} :=
  d3PointedKanParameterDiagram (d3TensorParameter D E)

/-- 任意の角への制限は、同じテンソルパラメータの元の内部 Hom 豊穣作用。 -/
lemma d3TensorParameterDiagram_stage (p : J × K) :
    (EnrichedOrderedCylinder.stageInclusion (C := PointedKanObject.{u}) p).comp SSet
      (d3TensorParameterDiagram D E) =
    d3PointedKanIhom (D.obj (Opposite.op p.1) ⊗ E.obj (Opposite.op p.2)) :=
  d3PointedKanParameterDiagram_stage (d3TensorParameter D E) p

/-- 元の二つの実端点四角形を、16 個のパラメータを持つ一つの図式へ束ねる。 -/
def d3DoubleEndpointParameter :
    ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))ᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  d3TensorParameter d3EndpointParameter d3EndpointParameter

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
